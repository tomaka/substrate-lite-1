// Smoldot
// Copyright (C) 2019-2021  Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use crate::libp2p::{
    self, connection, discovery::kademlia, multiaddr, peer_id, PeerId, QueueNotificationError,
};
use crate::network::{peerset, protocol};
use crate::util;

use alloc::{
    collections::BTreeSet,
    format,
    string::{String, ToString as _},
    vec::Vec,
};
use core::{
    fmt, iter,
    num::NonZeroUsize,
    ops::{Add, Sub},
    task::{Poll, Waker},
    time::Duration,
};
use futures::{lock::Mutex, prelude::*};
use rand::{Rng as _, RngCore as _, SeedableRng as _};

/// Configuration for a [`ChainNetwork`].
pub struct Config {
    /// Capacity to initially reserve to the list of connections.
    pub connections_capacity: usize,

    /// Capacity to initially reserve to the list of peers.
    pub peers_capacity: usize,

    /// Seed for the randomness within the networking state machine.
    ///
    /// While this seed influences the general behaviour of the networking state machine, it
    /// notably isn't used when generating the ephemeral key used for the Diffie-Hellman
    /// handshake.
    /// This is a defensive measure against users passing a dummy seed instead of actual entropy.
    pub randomness_seed: [u8; 32],

    /// List of blockchain peer-to-peer networks to be connected to.
    ///
    /// > **Note**: As documented in [the module-level documentation](..), the [`ChainNetwork`]
    /// >           can connect to multiple blockchain networks at the same time.
    ///
    /// The order in which the chains are list is important. The index of each entry needs to be
    /// used later in order to refer to a specific chain.
    pub chains: Vec<ChainConfig>,

    // TODO: what about letting API users insert nodes later?
    pub known_nodes: Vec<(peer_id::PeerId, multiaddr::Multiaddr)>,

    /// Key used for the encryption layer.
    /// This is a Noise static key, according to the Noise specification.
    /// Signed using the actual libp2p key.
    pub noise_key: connection::NoiseKey,

    /// Number of events that can be buffered internally before connections are back-pressured.
    ///
    /// A good default value is 64.
    ///
    /// # Context
    ///
    /// The [`ChainNetwork`] maintains an internal buffer of the events returned by
    /// [`ChainNetwork::next_event`]. When [`ChainNetwork::read_write`] is called, an event might
    /// get pushed to this buffer. If this buffer is full, back-pressure will be applied to the
    /// connections in order to prevent new events from being pushed.
    ///
    /// This value is important if [`ChainNetwork::next_event`] is called at a slower than the
    /// calls to [`ChainNetwork::read_write`] generate events.
    pub pending_api_events_buffer_size: NonZeroUsize,
}

/// Configuration for a specific overlay network.
///
/// See [`Config::chains`].
pub struct ChainConfig {
    /// Identifier of the protocol, used on the wire to determine which chain messages refer to.
    ///
    /// > **Note**: This value is typically found in the specification of the chain (the
    /// >           "chain spec").
    pub protocol_id: String,

    /// List of node identities that are known to belong to this overlay network. The node
    /// identities are indices in [`Config::known_nodes`].
    pub bootstrap_nodes: Vec<usize>,

    /// If `Some`, the chain uses the GrandPa networking protocol.
    pub grandpa_protocol_config: Option<GrandpaState>,

    pub in_slots: u32,

    pub out_slots: u32,

    /// Hash of the best block according to the local node.
    pub best_hash: [u8; 32],
    /// Height of the best block according to the local node.
    pub best_number: u64,
    /// Hash of the genesis block (i.e. block number 0) according to the local node.
    pub genesis_hash: [u8; 32],
    pub role: protocol::Role,
}

#[derive(Debug, Copy, Clone)]
// TODO: link to some doc about how GrandPa works: what is a round, what is the set id, etc.
pub struct GrandpaState {
    pub round_number: u64,
    /// Set of authorities that will be used by the node to try finalize the children of the block
    /// of [`GrandpaState::commit_finalized_height`].
    pub set_id: u64,
    /// Height of the highest block considered final by the node.
    pub commit_finalized_height: u32,
}

/// Identifier of a pending connection requested by the network through a [`StartConnect`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PendingId(usize);

/// Identifier of a connection spawned by the [`ChainNetwork`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConnectionId(libp2p::ConnectionId);

/// Data structure containing the list of all connections, pending or not, and their latest known
/// state. See also [the module-level documentation](..).
pub struct ChainNetwork<TNow> {
    /// Underlying data structure. Collection of connections.
    /// The "user data" associated to each connection is its identifier in [`Guarded::peerset`].
    libp2p: libp2p::Network<peerset::ConnectionId, TNow>,

    /// Extra fields protected by a `Mutex`.
    guarded: Mutex<Guarded>,

    /// See [`Config::chains`].
    chain_configs: Vec<ChainConfig>,

    /// Generator for randomness.
    randomness: Mutex<rand_chacha::ChaCha20Rng>,
}

struct Guarded {
    peerset: peerset::Peerset,

    /// In the [`ChainNetwork::next_event`] function, an event is grabbed from the underlying
    /// [`ChainNetwork::libp2p`]. This event might lead to some asynchronous post-processing
    /// being needed. Because the user can interrupt the future returned by
    /// [`ChainNetwork::next_event`] at any point in time, this post-processing cannot be
    /// immediately performed, as the user could could interrupt the future and lose the event.
    /// Instead, the necessary post-processing is stored in this field. This field is then
    /// processed before the next event is pulled.
    to_process_pre_event: Option<ToProcessPreEvent>,

    /// For each item in [`ChainNetwork::chain_configs`], the corresponding Grandpa state.
    ///
    /// The `Vec` always has the same length as [`ChainNetwork::chain_configs`]. The `Option`
    /// is `None` if the chain doesn't use the Grandpa protocol.
    chain_grandpa_config: Vec<Option<GrandpaState>>,

    // TODO: doc
    substream_open_waker: Option<Waker>,
}

/// See [`Guarded::to_process_pre_event`]
enum ToProcessPreEvent {
    AcceptNotificationsIn {
        connection_id: libp2p::ConnectionId,
        overlay_network_index: usize,
        handshake: Vec<u8>,
    },
    QueueNotification {
        connection_id: libp2p::ConnectionId,
        overlay_network_index: usize,
        packet: Vec<u8>,
    },
}

/// See [`Guarded::peers`].
struct Peer {
    /// Identity of this peer.
    peer_id: PeerId,

    /// List of addresses that we assume could be dialed to reach the peer.
    ///
    /// If the value is `Some`, a connection using that address can be found at the given index
    /// in [`Guarded::connections`].
    ///
    /// Does not include "dialing" addresses. For example, no address should contain an outgoing
    /// TCP port.
    known_addresses: hashbrown::HashMap<multiaddr::Multiaddr, Option<usize>, ahash::RandomState>,
}

/// See [`Guarded::connections`].
struct Connection {
    /// [`PeerId`] of the remote, or *expected* [`PeerId`] (which might end up being different
    /// from the actual) if the handshake isn't finished yet.
    peer_id: PeerId,

    /// Address on the other side of the connection.
    ///
    /// Will be found in [`Peer::known_addresses`] if and only if the connection is outbound.
    address: multiaddr::Multiaddr,

    /// `Some` if the connection with the remote has been reached. Contains extra fields.
    reached: Option<ConnectionReached>,
}

/// See [`Connection::reached`].
struct ConnectionReached {
    /// Identifier of this connection according to [`ChainNetwork::libp2p`].
    ///
    /// Since [`libp2p::ConnectionId`] are never re-used, .
    inner_id: libp2p::ConnectionId,
}

enum SubstreamState {
    Closed,
    OpeningOut,
    In,
}

// Update this when a new request response protocol is added.
const REQUEST_RESPONSE_PROTOCOLS_PER_CHAIN: usize = 4;
// Update this when a new notifications protocol is added.
const NOTIFICATIONS_PROTOCOLS_PER_CHAIN: usize = 3;

impl<TNow> ChainNetwork<TNow>
where
    TNow: Clone + Add<Duration, Output = TNow> + Sub<TNow, Output = Duration> + Ord,
{
    /// Initializes a new [`ChainNetwork`].
    pub fn new(config: Config) -> Self {
        // The order of protocols here is important, as it defines the values of `protocol_index`
        // to pass to libp2p or that libp2p produces.
        let overlay_networks = config
            .chains
            .iter()
            .flat_map(|chain| {
                iter::once(libp2p::OverlayNetworkConfig {
                    protocol_name: format!("/{}/block-announces/1", chain.protocol_id),
                    fallback_protocol_names: Vec::new(),
                    max_handshake_size: 256,      // TODO: arbitrary
                    max_notification_size: 32768, // TODO: arbitrary
                    bootstrap_nodes: chain.bootstrap_nodes.clone(),
                })
                .chain(iter::once(libp2p::OverlayNetworkConfig {
                    protocol_name: format!("/{}/transactions/1", chain.protocol_id),
                    fallback_protocol_names: Vec::new(),
                    max_handshake_size: 256,      // TODO: arbitrary
                    max_notification_size: 32768, // TODO: arbitrary
                    bootstrap_nodes: chain.bootstrap_nodes.clone(),
                }))
                .chain({
                    // The `has_grandpa_protocol` flag controls whether the chain uses GrandPa.
                    // Note, however, that GrandPa is technically left enabled (but unused) on all
                    // chains, in order to make the rest of the code of this module more
                    // comprehensible.
                    iter::once(libp2p::OverlayNetworkConfig {
                        protocol_name: "/paritytech/grandpa/1".to_string(),
                        fallback_protocol_names: Vec::new(),
                        max_handshake_size: 256,      // TODO: arbitrary
                        max_notification_size: 32768, // TODO: arbitrary
                        bootstrap_nodes: if chain.grandpa_protocol_config.is_some() {
                            chain.bootstrap_nodes.clone()
                        } else {
                            Vec::new()
                        },
                    })
                })
            })
            .collect();

        // The order of protocols here is important, as it defines the values of `protocol_index`
        // to pass to libp2p or that libp2p produces.
        let request_response_protocols = iter::once(libp2p::ConfigRequestResponse {
            name: "/ipfs/id/1.0.0".into(),
            inbound_config: libp2p::ConfigRequestResponseIn::Empty,
            max_response_size: 4096,
            inbound_allowed: true,
            timeout: Duration::from_secs(20),
        })
        .chain(config.chains.iter().flat_map(|chain| {
            // TODO: limits are arbitrary
            iter::once(libp2p::ConfigRequestResponse {
                name: format!("/{}/sync/2", chain.protocol_id),
                inbound_config: libp2p::ConfigRequestResponseIn::Payload { max_size: 1024 },
                max_response_size: 10 * 1024 * 1024,
                // TODO: make this configurable
                inbound_allowed: false,
                timeout: Duration::from_secs(20),
            })
            .chain(iter::once(libp2p::ConfigRequestResponse {
                name: format!("/{}/light/2", chain.protocol_id),
                inbound_config: libp2p::ConfigRequestResponseIn::Payload {
                    max_size: 1024 * 512,
                },
                max_response_size: 10 * 1024 * 1024,
                // TODO: make this configurable
                inbound_allowed: false,
                timeout: Duration::from_secs(20),
            }))
            .chain(iter::once(libp2p::ConfigRequestResponse {
                name: format!("/{}/kad", chain.protocol_id),
                inbound_config: libp2p::ConfigRequestResponseIn::Payload { max_size: 1024 },
                max_response_size: 1024 * 1024,
                // TODO: `false` here means we don't insert ourselves in the DHT, which is the polite thing to do for as long as Kad isn't implemented
                inbound_allowed: false,
                timeout: Duration::from_secs(20),
            }))
            .chain(iter::once(libp2p::ConfigRequestResponse {
                name: format!("/{}/sync/warp", chain.protocol_id),
                inbound_config: libp2p::ConfigRequestResponseIn::Payload { max_size: 32 },
                max_response_size: 128 * 1024 * 1024, // TODO: this is way too large at the moment ; see https://github.com/paritytech/substrate/pull/8578
                // We don't support inbound warp sync requests (yet).
                inbound_allowed: false,
                timeout: Duration::from_secs(20),
            }))
        }))
        .collect();

        let mut randomness = rand_chacha::ChaCha20Rng::from_seed(config.randomness_seed);
        let inner_randomness_seed = randomness.sample(rand::distributions::Standard);

        let chain_grandpa_config = config
            .chains
            .iter()
            .map(|chain| chain.grandpa_protocol_config)
            .collect();

        let mut peers_by_id = {
            let k0 = randomness.next_u64();
            let k1 = randomness.next_u64();
            let k2 = randomness.next_u64();
            let k3 = randomness.next_u64();
            hashbrown::HashMap::with_capacity_and_hasher(
                config.peers_capacity,
                ahash::RandomState::with_seeds(k0, k1, k2, k3),
            )
        };

        let mut peers = slab::Slab::with_capacity(config.peers_capacity);
        let mut peers_chain_memberships = BTreeSet::new();

        for (peer_id, multiaddr) in config.known_nodes {
            let peer_index = match peers_by_id.entry(peer_id) {
                hashbrown::hash_map::Entry::Occupied(entry) => *entry.get(),
                hashbrown::hash_map::Entry::Vacant(entry) => {
                    let known_addresses = {
                        let k0 = randomness.next_u64();
                        let k1 = randomness.next_u64();
                        let k2 = randomness.next_u64();
                        let k3 = randomness.next_u64();
                        hashbrown::HashMap::with_capacity_and_hasher(
                            0,
                            ahash::RandomState::with_seeds(k0, k1, k2, k3),
                        )
                    };

                    let peer_index = peers.insert(Peer {
                        peer_id: entry.key().clone(),
                        known_addresses,
                    });

                    // Register membership of this peer on this chain.
                    for chain_index in 0..config.chains.len() {
                        peers_chain_memberships.insert((chain_index, peer_index));
                    }

                    entry.insert(peer_index);
                    peer_index
                }
            };

            peers[peer_index]
                .known_addresses
                .entry(multiaddr)
                .or_insert(None);
        }

        ChainNetwork {
            libp2p: libp2p::Network::new(libp2p::Config {
                capacity: config.connections_capacity,
                request_response_protocols,
                noise_key: config.noise_key,
                randomness_seed: inner_randomness_seed,
                pending_api_events_buffer_size: config.pending_api_events_buffer_size,
                overlay_networks,
                ping_protocol: "/ipfs/ping/1.0.0".into(),
            }),
            guarded: Mutex::new(Guarded {
                peerset: peerset::Peerset::new(),
                to_process_pre_event: None,
                chain_grandpa_config,
                substream_open_waker: None,
            }),
            chain_configs: config.chains,
            randomness: Mutex::new(randomness),
        }
    }

    fn protocol_index(&self, chain_index: usize, protocol: usize) -> usize {
        1 + chain_index * REQUEST_RESPONSE_PROTOCOLS_PER_CHAIN + protocol
    }

    /// Returns the number of established TCP connections, both incoming and outgoing.
    // TODO: note about race
    pub async fn num_established_connections(&self) -> usize {
        self.libp2p.len().await
    }

    /// Returns the number of chains. Always equal to the length of [`Config::chains`].
    pub fn num_chains(&self) -> usize {
        self.chain_configs.len()
    }

    /// Adds an incoming connection to the state machine.
    ///
    /// This connection hasn't finished handshaking and the [`PeerId`] of the remote isn't known
    /// yet.
    ///
    /// After this function has returned, you must process the connection with
    /// [`ChainNetwork::read_write`].
    #[must_use]
    pub async fn add_incoming_connection(
        &self,
        local_listen_address: &multiaddr::Multiaddr,
        remote_addr: multiaddr::Multiaddr,
    ) -> ConnectionId {
        let mut guarded = self.guarded.lock().await;

        let local_connections_entry = guarded.connections.vacant_entry();

        let inner_id = self
            .libp2p
            .insert(false, local_connections_entry.key())
            .await;

        local_connections_entry.insert(Connection {
            address: remote_addr,
            peer_id: todo!(), // TODO: `None` or something
            reached: Some(ConnectionReached { inner_id }),
        });

        ConnectionId(inner_id)
    }

    /// Update the state of the local node with regards to GrandPa rounds.
    ///
    /// Calling this method does two things:
    ///
    /// - Send on all the active GrandPa substreams a "neighbor packet" indicating the state of
    ///   the local node.
    /// - Update the neighbor packet that is automatically sent to peers when a GrandPa substream
    ///   gets opened.
    ///
    /// In other words, calling this function atomically informs all the present and future peers
    /// of the state of the local node regarding the GrandPa protocol.
    ///
    /// > **Note**: The information passed as parameter isn't validated in any way by this method.
    ///
    /// # Panic
    ///
    /// Panics if `chain_index` is out of range, or if the chain has GrandPa disabled.
    ///
    pub async fn set_local_grandpa_state(&self, chain_index: usize, grandpa_state: GrandpaState) {
        let mut guarded = self.guarded.lock().await;

        // Store this state for later, in case we open new Grandpa substreams.
        *guarded.chain_grandpa_config[chain_index].as_mut().unwrap() = grandpa_state;

        // Bytes of the neighbor packet to send out.
        let packet = protocol::GrandpaNotificationRef::Neighbor(protocol::NeighborPacket {
            round_number: grandpa_state.round_number,
            set_id: grandpa_state.set_id,
            commit_finalized_height: grandpa_state.commit_finalized_height,
        })
        .scale_encoding()
        .fold(Vec::new(), |mut a, b| {
            a.extend_from_slice(b.as_ref());
            a
        });

        // Now sending out.
        // TODO: right now we just try to send to everyone no matter which substream is open, which is wasteful
        for (_, connection) in &guarded.connections {
            if let Some(reached) = connection.reached.as_ref() {
                // Ignore sending errors.
                let _ = self
                    .libp2p
                    .queue_notification(
                        reached.inner_id,
                        chain_index * NOTIFICATIONS_PROTOCOLS_PER_CHAIN + 2,
                        packet.clone(),
                    )
                    .await;
            }
        }
    }

    async fn request_connection_id(
        &self,
        target: &peer_id::PeerId,
    ) -> Option<libp2p::ConnectionId> {
        let guarded = self.guarded.lock().await;
        guarded.peerset.peer_main_established(&target)
    }

    /// Sends a blocks request to the given peer.
    // TODO: more docs
    pub async fn blocks_request(
        &self,
        now: TNow,
        target: &peer_id::PeerId,
        chain_index: usize,
        config: protocol::BlocksRequestConfig,
    ) -> Result<Vec<protocol::BlockData>, BlocksRequestError> {
        let connection_id =
            self.request_connection_id(target)
                .await
                .ok_or(BlocksRequestError::Request(
                    libp2p::RequestError::NotConnected,
                ))?;

        let request_data = protocol::build_block_request(config).fold(Vec::new(), |mut a, b| {
            a.extend_from_slice(b.as_ref());
            a
        });

        let response = self
            .libp2p
            .request(
                now,
                connection_id,
                self.protocol_index(chain_index, 0),
                request_data,
            )
            .map_err(BlocksRequestError::Request)
            .await?;

        protocol::decode_block_response(&response).map_err(BlocksRequestError::Decode)
    }

    pub async fn grandpa_warp_sync_request(
        &self,
        now: TNow,
        target: &peer_id::PeerId,
        chain_index: usize,
        begin_hash: [u8; 32],
    ) -> Result<protocol::GrandpaWarpSyncResponse, GrandpaWarpSyncRequestError> {
        let connection_id = self.request_connection_id(target).await.ok_or(
            GrandpaWarpSyncRequestError::Request(libp2p::RequestError::NotConnected),
        )?;

        let request_data = begin_hash.to_vec();

        let response = self
            .libp2p
            .request(
                now,
                connection_id,
                self.protocol_index(chain_index, 3),
                request_data,
            )
            .map_err(GrandpaWarpSyncRequestError::Request)
            .await?;

        protocol::decode_grandpa_warp_sync_response(&response)
            .map_err(GrandpaWarpSyncRequestError::Decode)
    }

    /// Sends a storage request to the given peer.
    // TODO: more docs
    pub async fn storage_proof_request(
        &self,
        now: TNow,
        target: &peer_id::PeerId,
        chain_index: usize,
        config: protocol::StorageProofRequestConfig<impl Iterator<Item = impl AsRef<[u8]>>>,
    ) -> Result<Vec<Vec<u8>>, StorageProofRequestError> {
        let connection_id =
            self.request_connection_id(target)
                .await
                .ok_or(StorageProofRequestError::Request(
                    libp2p::RequestError::NotConnected,
                ))?;

        let request_data =
            protocol::build_storage_proof_request(config).fold(Vec::new(), |mut a, b| {
                a.extend_from_slice(b.as_ref());
                a
            });

        let response = self
            .libp2p
            .request(
                now,
                connection_id,
                self.protocol_index(chain_index, 1),
                request_data,
            )
            .map_err(StorageProofRequestError::Request)
            .await?;

        protocol::decode_storage_proof_response(&response).map_err(StorageProofRequestError::Decode)
    }

    /// Sends a call proof request to the given peer.
    ///
    /// This request is similar to [`ChainNetwork::storage_proof_request`]. Instead of requesting
    /// specific keys, we request the list of all the keys that are accessed for a specific
    /// runtime call.
    ///
    /// There exists no guarantee that the proof is complete (i.e. that it contains all the
    /// necessary entries), as it is impossible to know this from just the proof itself. As such,
    /// this method is just an optimization. When performing the actual call, regular storage proof
    /// requests should be performed if the key is not present in the call proof response.
    pub async fn call_proof_request<'a>(
        &self,
        now: TNow,
        target: &peer_id::PeerId,
        chain_index: usize,
        config: protocol::CallProofRequestConfig<'a, impl Iterator<Item = impl AsRef<[u8]>>>,
    ) -> Result<Vec<Vec<u8>>, CallProofRequestError> {
        let connection_id =
            self.request_connection_id(target)
                .await
                .ok_or(CallProofRequestError::Request(
                    libp2p::RequestError::NotConnected,
                ))?;

        let request_data =
            protocol::build_call_proof_request(config).fold(Vec::new(), |mut a, b| {
                a.extend_from_slice(b.as_ref());
                a
            });

        let response = self
            .libp2p
            .request(
                now,
                connection_id,
                self.protocol_index(chain_index, 1),
                request_data,
            )
            .map_err(CallProofRequestError::Request)
            .await?;

        protocol::decode_call_proof_response(&response).map_err(CallProofRequestError::Decode)
    }

    ///
    ///
    /// Must be passed the double-SCALE-encoded transaction.
    pub async fn announce_transaction(
        &self,
        target: &peer_id::PeerId,
        chain_index: usize,
        extrinsic: &[u8],
    ) -> Result<(), QueueNotificationError> {
        // TODO: no, don't use request_connection_id, must have a substream open
        let connection_id = self
            .request_connection_id(target)
            .await
            .ok_or(QueueNotificationError::NotConnected)?;

        let mut val = Vec::with_capacity(1 + extrinsic.len());
        val.extend_from_slice(util::encode_scale_compact_usize(1).as_ref());
        val.extend_from_slice(extrinsic);
        self.libp2p
            .queue_notification(
                connection_id,
                chain_index * NOTIFICATIONS_PROTOCOLS_PER_CHAIN + 1,
                val,
            )
            .await
    }

    /// After calling [`ChainNetwork::fill_out_slots`], notifies the [`ChainNetwork`] of the
    /// success of the dialing attempt.
    ///
    /// See also [`ChainNetwork::pending_outcome_err`].
    ///
    /// After this function has returned, you must process the connection with
    /// [`ChainNetwork::read_write`].
    ///
    /// # Panic
    ///
    /// Panics if the [`PendingId`] is invalid.
    ///
    #[must_use]
    pub async fn pending_outcome_ok(&self, id: PendingId) -> ConnectionId {
        let mut guarded = self.guarded.lock().await;

        let mut connection = &mut guarded.connections[id.0];

        // Must check that the connected referred to by `id` is indeed correct.
        // Since `connections` shares both pending and established connections, the `PendingId` is
        // only correctly if `reached` is `None`.
        assert!(connection.reached.is_none());

        let inner_id = self.libp2p.insert(true, id.0).await;

        connection.reached = Some(ConnectionReached { inner_id });

        ConnectionId(inner_id)
    }

    /// After calling [`ChainNetwork::fill_out_slots`], notifies the [`ChainNetwork`] of the
    /// failure of the dialing attempt.
    ///
    /// See also [`ChainNetwork::pending_outcome_ok`].
    ///
    /// # Panic
    ///
    /// Panics if the [`PendingId`] is invalid.
    ///
    pub async fn pending_outcome_err(&self, id: PendingId) {
        let mut guarded = self.guarded.lock().await;

        // Must check that the connected referred to by `id` is indeed correct.
        // Since `connections` shares both pending and established connections, the `PendingId` is
        // only correctly if `reached` is `None`.
        assert!(guarded.connections[id.0].reached.is_none());

        // Kill that connection altogether.
        let removed = guarded.connections.remove(id.0);

        // TODO: finish
        todo!()

        //guarded.peers_connections.remove(removed.peer_id);
    }

    /// Returns the next event produced by the service.
    ///
    /// This function should be called at a high enough rate that [`ChainNetwork::read_write`] can
    /// continue pushing events to the internal buffer of events. Failure to call this function
    /// often enough will lead to connections being back-pressured.
    /// See also [`Config::pending_api_events_buffer_size`].
    ///
    /// It is technically possible to call this function multiple times simultaneously, in which
    /// case the events will be distributed amongst the multiple calls in an unspecified way.
    /// Keep in mind that some [`Event`]s have logic attached to the order in which they are
    /// produced, and calling this function multiple times is therefore discouraged.
    pub async fn next_event<'a>(&'a self) -> Event<'a, TNow> {
        loop {
            // The objective of the block of code below is to retrieve the next event that
            // happened on the underlying libp2p state machine by calling
            // `self.libp2p.next_event()`.
            //
            // After an event has been grabbed from `self.libp2p`, some modifications will need to
            // be performed in `self.guarded`. Since it can take a lot of time to retrieve an
            // event, and since other methods of `ChainNetwork` need to lock `self.guarded`, it
            // is undesirable to keep `self.guarded` locked while waiting for the
            // `self.libp2p.next_event()` future to finish.
            //
            // A naive solution would be to grab an event from `self.libp2p` then lock
            // `self.guarded` immediately after. Unfortunately, the user can technically call
            // `next_event` multiple times simultaneously. If that is done, we want to avoid a
            // situation where task A retrieves an event, then task B retrieves an event, then
            // task B locks `self.guarded` before task A could. Some kind of locking must be
            // performed to prevent this.
            //
            // Additionally, `guarded` contains some fields, such as `to_process_pre_event`, that
            // need to be processed ahead of events. Because processing these fields requires
            // using `await`, this processing can be interrupted by the user, and as such no event
            // should be grabbed in that situation.
            //
            // For all these reasons, the logic of the code below is as follows:
            //
            // - First, asynchronously lock `self.guarded`.
            // - After `self.guarded` is locked, if some of its fields require ahead-of-events
            // processing, continue with `maybe_inner_event` equal to `None`.
            // - Otherwise, and while `self.guarded` is still locked, try to immediately grab an
            // event with `self.libp2p.next_event()`.
            // - If no such event is immediately available, register the task waker and release
            // the lock. Once the waker is invoked (meaning that an event should be available),
            // go back to step 1 (locking `self.guarded`).
            // - If an event is available, continue with `maybe_inner_event` equal to `Some`.
            //
            let (mut guarded, maybe_inner_event) = {
                let next_event_future = self.libp2p.next_event();
                futures::pin_mut!(next_event_future);

                let mut lock_acq_future = self.guarded.lock();
                future::poll_fn(move |cx| {
                    let lock = match lock_acq_future.poll_unpin(cx) {
                        Poll::Ready(l) => l,
                        Poll::Pending => return Poll::Pending,
                    };

                    if lock.to_process_pre_event.is_some() {
                        return Poll::Ready((lock, None));
                    }

                    match next_event_future.poll_unpin(cx) {
                        Poll::Ready(event) => Poll::Ready((lock, Some(event))),
                        Poll::Pending => {
                            lock_acq_future = self.guarded.lock();
                            Poll::Pending
                        }
                    }
                })
                .await
            };
            let mut guarded = &mut *guarded; // Avoid borrow checker issues.

            // If `maybe_inner_event` is `None`, that means some ahead-of-events processing needs
            // to be performed. No event has been grabbed from `self.libp2p`.
            let inner_event: libp2p::Event<_> = match maybe_inner_event {
                Some(ev) => ev,
                None => {
                    // We can't use `take()` because the call to `accept_notifications_in` might
                    // be interrupted by the user. The field is set to `None` only after the call
                    // has succeeded.
                    match guarded.to_process_pre_event.as_ref().unwrap() {
                        ToProcessPreEvent::AcceptNotificationsIn {
                            connection_id,
                            overlay_network_index,
                            handshake,
                        } => {
                            self.libp2p
                                .accept_notifications_in(
                                    *connection_id,
                                    *overlay_network_index,
                                    handshake.clone(), // TODO: clone? :-/
                                )
                                .await;
                        }
                        ToProcessPreEvent::QueueNotification {
                            connection_id,
                            overlay_network_index,
                            packet,
                        } => {
                            let _ = self
                                .libp2p
                                .queue_notification(
                                    *connection_id,
                                    *overlay_network_index,
                                    packet.clone(),
                                ) // TODO: clone? :-/
                                .await;
                        }
                    }

                    guarded.to_process_pre_event = None;
                    continue;
                }
            };

            // An event has been grabbed and is ready to be processed. `self.guarded` is still
            // locked from before the event has been grabbed.
            // In order to avoid futures cancellation issues, no `await` should be used below. If
            // something requires asynchronous processing, it should instead be written to
            // `self.to_process_pre_event`.
            debug_assert!(guarded.to_process_pre_event.is_none());

            // `PeerId` of the connection concerned by the event, or expected `PeerId` if the
            // connection hasn't yet finished its handshake.
            let peer_id = &guarded
                .connections
                .get(*inner_event.user_data())
                .unwrap()
                .peer_id;

            match inner_event {
                libp2p::Event::HandshakeFinished {
                    id: connection_id,
                    peer_id: actual_peer_id,
                    user_data: local_connection_index,
                } => {
                    if *peer_id != actual_peer_id {
                        todo!() // TODO:
                    }

                    // TODO: need to handle incoming connections properly here

                    if let Some(waker) = guarded.substream_open_waker.take() {
                        waker.wake();
                    }

                    return Event::Connected(actual_peer_id);
                }

                libp2p::Event::Shutdown {
                    id: connection_id,
                    mut out_overlay_network_indices,
                    user_data: local_connection_index,
                    ..
                } => {
                    let peer_id = peer_id.clone();

                    // Remove this connection from the local state in `guarded`.
                    let _removed_connection = guarded.connections.remove(local_connection_index);
                    debug_assert_eq!(_removed_connection.reached.unwrap().inner_id, connection_id);
                    debug_assert_eq!(_removed_connection.peer_id, peer_id);
                    let peer_index = *guarded.peers_by_id.get(&peer_id).unwrap();
                    let _was_removed = guarded
                        .peers_connections
                        .remove(&(peer_index, local_connection_index));
                    debug_assert!(_was_removed);

                    // Adjust `out_overlay_network_indices` to become `chain_indices`.
                    let chain_indices = {
                        out_overlay_network_indices
                            .retain(|i| (i % NOTIFICATIONS_PROTOCOLS_PER_CHAIN) == 0);
                        for elem in &mut out_overlay_network_indices {
                            *elem /= NOTIFICATIONS_PROTOCOLS_PER_CHAIN;
                        }
                        out_overlay_network_indices
                    };

                    for chain_index in &chain_indices {
                        // TODO: use guarded.peers_chain_memberships
                    }

                    if let Some(waker) = guarded.substream_open_waker.take() {
                        waker.wake();
                    }

                    return Event::Disconnected {
                        peer_id,
                        chain_indices,
                    };
                }

                libp2p::Event::RequestIn {
                    id,
                    substream_id,
                    protocol_index,
                    user_data: local_connection_index,
                    ..
                } => {
                    // Only protocol 0 (identify) can receive requests at the moment.
                    debug_assert_eq!(protocol_index, 0);

                    return Event::IdentifyRequestIn {
                        peer_id: peer_id.clone(),
                        request: IdentifyRequestIn {
                            service: self,
                            id,
                            connection_index: local_connection_index,
                            substream_id,
                        },
                    };
                }

                libp2p::Event::NotificationsOutAccept {
                    id: connection_id,
                    overlay_network_index,
                    remote_handshake,
                    user_data: local_connection_index,
                    ..
                } => {
                    let chain_index = overlay_network_index / NOTIFICATIONS_PROTOCOLS_PER_CHAIN;
                    if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 0 {
                        let remote_handshake =
                            match protocol::decode_block_announces_handshake(&remote_handshake) {
                                Ok(hs) => hs,
                                Err(err) => {
                                    // TODO: close the substream?
                                    return Event::ProtocolError {
                                        peer_id: peer_id.clone(),
                                        error: ProtocolError::BadBlockAnnouncesHandshake(err),
                                    };
                                }
                            };

                        // TODO: compare genesis hash with ours

                        let peer_index = *guarded.peers_by_id.get(peer_id).unwrap();
                        if guarded
                            .peers_connections
                            .insert((peer_index, local_connection_index))
                        {
                            for other_overlay_network_index in (1
                                ..NOTIFICATIONS_PROTOCOLS_PER_CHAIN)
                                .map(|n| chain_index * NOTIFICATIONS_PROTOCOLS_PER_CHAIN + n)
                            {
                                let _was_inserted = guarded
                                    .peers_missing_out_substreams
                                    .insert((peer_index, other_overlay_network_index));
                                debug_assert!(_was_inserted);
                            }

                            return Event::ChainConnected {
                                peer_id: peer_id.clone(),
                                chain_index,
                                best_hash: *remote_handshake.best_hash,
                                best_number: remote_handshake.best_number,
                                role: remote_handshake.role,
                            };
                        }
                    } else if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 1 {
                        // Nothing to do.
                    } else if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 2 {
                        // Grandpa notification has been opened. Send neighbor packet.
                        let grandpa_config = guarded.chain_grandpa_config[chain_index]
                            .as_ref()
                            .unwrap()
                            .clone();
                        let packet =
                            protocol::GrandpaNotificationRef::Neighbor(protocol::NeighborPacket {
                                round_number: grandpa_config.round_number,
                                set_id: grandpa_config.set_id,
                                commit_finalized_height: grandpa_config.commit_finalized_height,
                            })
                            .scale_encoding()
                            .fold(Vec::new(), |mut a, b| {
                                a.extend_from_slice(b.as_ref());
                                a
                            });

                        // Sending the notification isn't done immediately because of
                        // futures-cancellation-related concerns.
                        debug_assert!(guarded.to_process_pre_event.is_none());
                        guarded.to_process_pre_event = Some(ToProcessPreEvent::QueueNotification {
                            connection_id,
                            overlay_network_index,
                            packet,
                        });
                    } else {
                        unreachable!()
                    }

                    // TODO:
                }

                libp2p::Event::NotificationsOutClose {
                    overlay_network_index,
                    user_data: local_connection_index,
                    ..
                } => {
                    let chain_index = overlay_network_index / NOTIFICATIONS_PROTOCOLS_PER_CHAIN;
                    let peer_index = *guarded.peers_by_id.get(peer_id).unwrap();

                    if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 0 {
                        let _was_removed = guarded
                            .peers_connections
                            .remove(&(peer_index, local_connection_index));
                        debug_assert!(_was_removed);

                        for other_overlay_network_index in (1..NOTIFICATIONS_PROTOCOLS_PER_CHAIN)
                            .map(|n| chain_index * NOTIFICATIONS_PROTOCOLS_PER_CHAIN + n)
                        {
                            guarded
                                .peers_missing_out_substreams
                                .remove(&(peer_index, other_overlay_network_index));
                        }

                        return Event::ChainDisconnected {
                            peer_id: peer_id.clone(),
                            chain_index,
                        };
                    } else {
                        if guarded
                            .peers_connections
                            .contains(&(peer_index, local_connection_index))
                        {
                            let _was_inserted = guarded
                                .peers_missing_out_substreams
                                .insert((peer_index, overlay_network_index));
                            debug_assert!(_was_inserted);
                        }
                    }

                    if let Some(waker) = guarded.substream_open_waker.take() {
                        waker.wake();
                    }
                }

                libp2p::Event::NotificationsInOpen {
                    id: connection_id,
                    overlay_network_index,
                    remote_handshake,
                    user_data: local_connection_index,
                } => {
                    // Remote requests to open a notifications substream.

                    let chain_index = overlay_network_index / NOTIFICATIONS_PROTOCOLS_PER_CHAIN;

                    if (overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN) == 0 {
                        if let Err(err) =
                            protocol::decode_block_announces_handshake(&remote_handshake)
                        {
                            // TODO: self.libp2p.refuse_notifications_in(*id, *overlay_network_index);
                            return Event::ProtocolError {
                                peer_id: peer_id.clone(),
                                error: ProtocolError::BadBlockAnnouncesHandshake(err),
                            };
                        }

                        let chain_config = &self.chain_configs[chain_index];
                        let handshake = protocol::encode_block_announces_handshake(
                            protocol::BlockAnnouncesHandshakeRef {
                                best_hash: &chain_config.best_hash,
                                best_number: chain_config.best_number,
                                genesis_hash: &chain_config.genesis_hash,
                                role: chain_config.role,
                            },
                        )
                        .fold(Vec::new(), |mut a, b| {
                            a.extend_from_slice(b.as_ref());
                            a
                        });

                        // Accepting the substream isn't done immediately because of
                        // futures-cancellation-related concerns.
                        debug_assert!(guarded.to_process_pre_event.is_none());
                        guarded.to_process_pre_event =
                            Some(ToProcessPreEvent::AcceptNotificationsIn {
                                connection_id,
                                handshake,
                                overlay_network_index,
                            });
                    } else if (overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN) == 1 {
                        // Accepting the substream isn't done immediately because of
                        // futures-cancellation-related concerns.
                        debug_assert!(guarded.to_process_pre_event.is_none());
                        guarded.to_process_pre_event =
                            Some(ToProcessPreEvent::AcceptNotificationsIn {
                                connection_id,
                                handshake: Vec::new(),
                                overlay_network_index,
                            });
                    } else if (overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN) == 2 {
                        // Grandpa substream.
                        let handshake = self.chain_configs[chain_index]
                            .role
                            .scale_encoding()
                            .to_vec();

                        // Accepting the substream isn't done immediately because of
                        // futures-cancellation-related concerns.
                        debug_assert!(guarded.to_process_pre_event.is_none());
                        guarded.to_process_pre_event =
                            Some(ToProcessPreEvent::AcceptNotificationsIn {
                                connection_id,
                                handshake,
                                overlay_network_index,
                            });
                    } else {
                        unreachable!()
                    }
                }

                libp2p::Event::NotificationsIn {
                    id: connection_id,
                    overlay_network_index,
                    notification,
                    user_data: local_connection_index,
                    ..
                } => {
                    // Don't report events about nodes we don't have an outbound substream with.
                    // TODO: think about possible race conditions regarding missing block
                    // announcements, as the remote will think we know it's at a certain block
                    // while we ignored its announcement ; it isn't problematic as long as blocks
                    // are generated continuously, as announcements will be generated periodically
                    // as well and the state will no longer mismatch
                    // TODO: restore ^

                    let chain_index = overlay_network_index / NOTIFICATIONS_PROTOCOLS_PER_CHAIN;
                    if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 0 {
                        if let Err(err) = protocol::decode_block_announce(&notification) {
                            return Event::ProtocolError {
                                peer_id: peer_id.clone(),
                                error: ProtocolError::BadBlockAnnounce(err),
                            };
                        }

                        return Event::BlockAnnounce {
                            chain_index,
                            peer_id: peer_id.clone(),
                            announce: EncodedBlockAnnounce(notification),
                        };
                    } else if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 1 {
                        // TODO: transaction announce
                    } else if overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 2 {
                        let decoded_notif =
                            match protocol::decode_grandpa_notification(&notification) {
                                Ok(n) => n,
                                Err(err) => {
                                    return Event::ProtocolError {
                                        peer_id: peer_id.clone(),
                                        error: ProtocolError::BadGrandpaNotification(err),
                                    };
                                }
                            };

                        // Commit messages are the only type of message that is important for
                        // light clients. Anything else is presently ignored.
                        if let protocol::GrandpaNotificationRef::Commit(_) = decoded_notif {
                            return Event::GrandpaCommitMessage {
                                chain_index,
                                message: EncodedGrandpaCommitMessage(notification),
                            };
                        }
                    } else {
                        unreachable!()
                    }
                }

                libp2p::Event::NotificationsInClose {
                    id,
                    overlay_network_index,
                    user_data: local_connection_index,
                    ..
                } => {
                    // TODO: ?

                    if let Some(waker) = guarded.substream_open_waker.take() {
                        waker.wake();
                    }
                }
            }
        }
    }

    /// Performs a round of Kademlia discovery.
    ///
    /// This future yields once a list of nodes on the network has been discovered, or a problem
    /// happened.
    pub async fn kademlia_discovery_round(
        &'_ self,
        now: TNow,
        chain_index: usize,
    ) -> Result<DiscoveryInsert<'_, TNow>, DiscoveryError> {
        let random_peer_id = {
            let mut randomness = self.randomness.lock().await;
            let pub_key = randomness.sample(rand::distributions::Standard);
            peer_id::PeerId::from_public_key(&peer_id::PublicKey::Ed25519(pub_key))
        };

        // Select a random peer to query.

        let request_data = kademlia::build_find_node_request(random_peer_id.as_bytes());
        /*if let Some(target) = self.libp2p.peers_list_lock().await.next() {
            // TODO: better peer selection
            let response = self
                .libp2p
                .request(
                    now,
                    target,
                    self.protocol_index(chain_index, 2),
                    request_data,
                )
                .await
                .map_err(DiscoveryError::RequestFailed)?;
            let decoded = kademlia::decode_find_node_response(&response)
                .map_err(DiscoveryError::DecodeError)?;
            Ok(DiscoveryInsert {
                service: self,
                outcome: decoded,
                chain_index,
            })
        } else {*/
        Err(DiscoveryError::NoPeer)
        //}
    }

    /// Waits until a connection is in a state in which a substream can be opened.
    pub async fn next_substream<'a>(&'a self) -> SubstreamOpen<'a, TNow> {
        loop {
            let guarded = self.guarded.lock().await;

            // TODO: O(n) :-/
            for chain_index in 0..self.chain_configs.len() {
                // Grab node for which we have an established outgoing connections but haven't yet
                // opened a substream to.
                for &(_, peer_index) in guarded
                    .peers_chain_memberships
                    .range((chain_index, usize::min_value())..=(chain_index, usize::max_value()))
                {
                    for &(_, connection_index) in guarded
                        .peers_connections
                        .range((peer_index, usize::min_value())..=(peer_index, usize::max_value()))
                    {
                        let connection = &guarded.connections[connection_index];

                        let connection_id = match connection.reached.as_ref() {
                            Some(r) => r.inner_id,
                            None => continue,
                        };

                        // TODO: filter out if no substream yet

                        return SubstreamOpen {
                            libp2p: &self.libp2p,
                            chain_configs: &self.chain_configs,
                            connection_id,
                            overlay_network_index: chain_index, // TODO: no
                        };
                    }
                }
            }

            // TODO: explain
            // TODO: if `next_substream` is called multiple times simultaneously, all but the first will deadlock
            let mut guarded = Some(guarded);
            future::poll_fn(move |cx| {
                if let Some(mut guarded) = guarded.take() {
                    guarded.substream_open_waker = Some(cx.waker().clone());
                    Poll::Pending
                } else {
                    Poll::Ready(())
                }
            })
            .await;
        }
    }

    /// Spawns new outgoing connections in order to fill empty outgoing slots.
    // TODO: shouldn't return an `Option`? should instead just wait instead of returning `None`?
    // TODO: give more control, with number of slots and node choice
    pub async fn fill_out_slots<'a>(&self, chain_index: usize) -> Option<StartConnect> {
        let mut guarded = self.guarded.lock().await;
        let guarded = &mut *guarded; // Solves borrow checker issues.

        // TODO: limit number of slots

        for &(_, peer_index) in guarded
            .peers_chain_memberships
            .range((chain_index, usize::min_value())..=(chain_index, usize::max_value()))
        {
            if guarded.peers[peer_index].known_addresses.is_empty() {
                continue;
            }

            if guarded.peers[peer_index]
                .known_addresses
                .values()
                .any(|a| a.is_some())
            {
                continue;
            }

            if guarded
                .peers_open_chains
                .contains(&(peer_index, chain_index))
            {
                continue;
            }

            let peer_id = guarded.peers[peer_index].peer_id.clone();

            let (multiaddr, pending_id_store) = guarded.peers[peer_index]
                .known_addresses
                .iter_mut()
                .next()
                .unwrap();

            let pending_id = guarded.connections.insert(Connection {
                address: multiaddr.clone(),
                peer_id: peer_id.clone(),
                reached: None,
            });

            *pending_id_store = Some(pending_id);

            return Some(StartConnect {
                id: PendingId(pending_id),
                multiaddr: multiaddr.clone(),
                expected_peer_id: peer_id,
            });
        }

        None
    }

    ///
    /// # Panic
    ///
    /// Panics if `connection_id` isn't a valid connection.
    ///
    pub async fn read_write<'a>(
        &self,
        connection_id: ConnectionId,
        now: TNow,
        incoming_buffer: Option<&[u8]>,
        outgoing_buffer: (&'a mut [u8], &'a mut [u8]),
    ) -> Result<ReadWrite<TNow>, libp2p::ConnectionError> {
        let inner = self
            .libp2p
            .read_write(connection_id.0, now, incoming_buffer, outgoing_buffer)
            .await?;
        Ok(ReadWrite {
            read_bytes: inner.read_bytes,
            written_bytes: inner.written_bytes,
            wake_up_after: inner.wake_up_after,
            wake_up_future: inner.wake_up_future,
            write_close: inner.write_close,
        })
    }

    /// Returns an iterator to the list of [`PeerId`]s that we have an established connection
    /// with.
    // TODO: this doesn't do what it says it does
    pub async fn peers_list(&self) -> impl Iterator<Item = PeerId> {
        let guarded = self.guarded.lock().await;
        guarded
            .peers_by_id
            .keys()
            .cloned()
            .collect::<Vec<_>>()
            .into_iter()
    }
}

/// User must start connecting to the given multiaddress.
///
/// Either [`ChainNetwork::pending_outcome_ok`] or [`ChainNetwork::pending_outcome_err`] must
/// later be called in order to inform of the outcome of the connection.
#[derive(Debug)]
#[must_use]
pub struct StartConnect {
    pub id: PendingId,
    pub multiaddr: multiaddr::Multiaddr,
    /// [`PeerId`] that is expected to be reached with this connection attempt.
    pub expected_peer_id: PeerId,
}

/// Event generated by [`ChainNetwork::next_event`].
#[derive(Debug)]
pub enum Event<'a, TNow> {
    /// Established a transport-level connection (e.g. a TCP socket) with the given peer.
    Connected(peer_id::PeerId),

    /// A transport-level connection (e.g. a TCP socket) has been closed.
    ///
    /// This event is called unconditionally when a connection with the given peer has been
    /// closed. If `chain_indices` isn't empty, this event is also equivalent to one or more
    /// [`Event::ChainDisconnected`] events.
    Disconnected {
        peer_id: peer_id::PeerId,
        chain_indices: Vec<usize>,
    },

    ChainConnected {
        chain_index: usize,
        peer_id: peer_id::PeerId,
        /// Role the node reports playing on the network.
        role: protocol::Role,
        /// Height of the best block according to this node.
        best_number: u64,
        /// Hash of the best block according to this node.
        best_hash: [u8; 32],
    },
    ChainDisconnected {
        peer_id: peer_id::PeerId,
        chain_index: usize,
    },

    /// Received a new block announce from a peer.
    ///
    /// Can only happen after a [`Event::ChainConnected`] with the given `PeerId` and chain index
    /// combination has happened.
    BlockAnnounce {
        /// Identity of the sender of the block announce.
        peer_id: peer_id::PeerId,
        /// Index of the chain the block relates to.
        chain_index: usize,
        announce: EncodedBlockAnnounce,
    },

    /// Received a GrandPa commit message from the network.
    GrandpaCommitMessage {
        /// Index of the chain the commit message relates to.
        chain_index: usize,
        message: EncodedGrandpaCommitMessage,
    },

    /// Error in the protocol in a connection, such as failure to decode a message.
    // TODO: explain consequences
    ProtocolError {
        /// Peer that has caused the protocol error.
        peer_id: peer_id::PeerId,
        /// Error that happened.
        error: ProtocolError,
    },

    /// A remote has sent a request for identification information.
    ///
    /// You are strongly encouraged to call [`IdentifyRequestIn::respond`].
    IdentifyRequestIn {
        /// Remote that has sent the request.
        peer_id: PeerId,
        /// Object allowing sending back the answer.
        request: IdentifyRequestIn<'a, TNow>,
    },
    /*Transactions {
        peer_id: peer_id::PeerId,
        transactions: EncodedTransactions,
    }*/
}

/// Undecoded but valid block announce handshake.
pub struct EncodedBlockAnnounceHandshake(Vec<u8>);

impl EncodedBlockAnnounceHandshake {
    /// Returns the decoded version of the handshake.
    pub fn decode(&self) -> protocol::BlockAnnouncesHandshakeRef {
        protocol::decode_block_announces_handshake(&self.0).unwrap()
    }
}

impl fmt::Debug for EncodedBlockAnnounceHandshake {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.decode(), f)
    }
}

/// Undecoded but valid block announce.
#[derive(Clone)]
pub struct EncodedBlockAnnounce(Vec<u8>);

impl EncodedBlockAnnounce {
    /// Returns the decoded version of the announcement.
    pub fn decode(&self) -> protocol::BlockAnnounceRef {
        protocol::decode_block_announce(&self.0).unwrap()
    }
}

impl fmt::Debug for EncodedBlockAnnounce {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.decode(), f)
    }
}

/// Undecoded but valid GrandPa commit message.
#[derive(Clone)]
pub struct EncodedGrandpaCommitMessage(Vec<u8>);

impl EncodedGrandpaCommitMessage {
    /// Returns the encoded bytes of the commit message.
    pub fn as_encoded(&self) -> &[u8] {
        // Skip the first byte because `self.0` is a `GrandpaNotificationRef`.
        &self.0[1..]
    }

    /// Returns the decoded version of the commit message.
    pub fn decode(&self) -> protocol::CommitMessageRef {
        match protocol::decode_grandpa_notification(&self.0) {
            Ok(protocol::GrandpaNotificationRef::Commit(msg)) => msg,
            _ => unreachable!(),
        }
    }
}

impl fmt::Debug for EncodedGrandpaCommitMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.decode(), f)
    }
}

/// Successfull outcome to [`ChainNetwork::kademlia_discovery_round`].
#[must_use]
pub struct DiscoveryInsert<'a, TNow> {
    service: &'a ChainNetwork<TNow>,
    outcome: Vec<(peer_id::PeerId, Vec<multiaddr::Multiaddr>)>,

    /// Index within [`Config::chains`] corresponding to the chain the nodes belong to.
    chain_index: usize,
}

impl<'a, TNow> DiscoveryInsert<'a, TNow>
where
    TNow: Clone + Add<Duration, Output = TNow> + Sub<TNow, Output = Duration> + Ord,
{
    /// Returns the list of [`peer_id::PeerId`]s that will be inserted.
    pub fn peer_ids(&self) -> impl Iterator<Item = &peer_id::PeerId> {
        self.outcome.iter().map(|(peer_id, _)| peer_id)
    }

    /// Insert the results in the [`ChainNetwork`].
    pub async fn insert(self) {
        let mut guarded = self.service.guarded.lock().await;
        let guarded = &mut *guarded; // Avoids borrow checker issues.

        for (peer_id, addrs) in self.outcome {
            let peer_index = match guarded.peers_by_id.entry(peer_id) {
                hashbrown::hash_map::Entry::Occupied(entry) => *entry.get(),
                hashbrown::hash_map::Entry::Vacant(entry) => {
                    let known_addresses = {
                        let mut randomness = self.service.randomness.lock().await;
                        let k0 = randomness.next_u64();
                        let k1 = randomness.next_u64();
                        let k2 = randomness.next_u64();
                        let k3 = randomness.next_u64();
                        hashbrown::HashMap::with_capacity_and_hasher(
                            addrs.len(),
                            ahash::RandomState::with_seeds(k0, k1, k2, k3),
                        )
                    };

                    let peer_index = guarded.peers.insert(Peer {
                        peer_id: entry.key().clone(),
                        known_addresses,
                    });

                    entry.insert(peer_index);
                    peer_index
                }
            };

            let peer = &mut guarded.peers[peer_index];
            peer.known_addresses.reserve(addrs.len());
            for address in addrs {
                peer.known_addresses.entry(address).or_insert(None);
            }

            // Register membership of this peer on this chain.
            guarded
                .peers_chain_memberships
                .insert((self.chain_index, peer_index));
        }
    }
}

/// Outcome of calling [`ChainNetwork::read_write`].
pub struct ReadWrite<TNow> {
    /// Number of bytes at the start of the incoming buffer that have been processed. These bytes
    /// should no longer be present the next time [`ChainNetwork::read_write`] is called.
    pub read_bytes: usize,

    /// Number of bytes written to the outgoing buffer. These bytes should be sent out to the
    /// remote. The rest of the outgoing buffer is left untouched.
    pub written_bytes: usize,

    /// If `Some`, [`ChainNetwork::read_write`] should be called again when the point in time
    /// reaches the value in the `Option`.
    pub wake_up_after: Option<TNow>,

    /// [`ChainNetwork::read_write`] should be called again when this
    /// [`libp2p::ConnectionReadyFuture`] returns `Ready`.
    pub wake_up_future: libp2p::ConnectionReadyFuture,

    /// If `true`, the writing side the connection must be closed. Will always remain to `true`
    /// after it has been set.
    ///
    /// If, after calling [`ChainNetwork::read_write`], the returned [`ReadWrite`] contains `true`
    /// here, and the inbound buffer is `None`, then the [`ConnectionId`] is now invalid.
    pub write_close: bool,
}

#[must_use]
pub struct SubstreamOpen<'a, TNow> {
    /// Connection to open a substream on.
    connection_id: libp2p::ConnectionId,

    /// Index of the overlay network, according to the underlying libp2p state machine.
    overlay_network_index: usize,

    /// Same as [`ChainNetwork::libp2p`].
    libp2p: &'a libp2p::Network<peerset::ConnectionId, TNow>,

    /// Same as [`ChainNetwork::chain_configs`].
    chain_configs: &'a Vec<ChainConfig>,
}

impl<'a, TNow> SubstreamOpen<'a, TNow>
where
    TNow: Clone + Add<Duration, Output = TNow> + Sub<TNow, Output = Duration> + Ord,
{
    /// Start the substream opening. Nothing is done as long as this method isn't called.
    pub async fn open(self, now: TNow) {
        let chain_config =
            &self.chain_configs[self.overlay_network_index / NOTIFICATIONS_PROTOCOLS_PER_CHAIN];

        let handshake = if self.overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 0 {
            protocol::encode_block_announces_handshake(protocol::BlockAnnouncesHandshakeRef {
                best_hash: &chain_config.best_hash,
                best_number: chain_config.best_number,
                genesis_hash: &chain_config.genesis_hash,
                role: chain_config.role,
            })
            .fold(Vec::new(), |mut a, b| {
                a.extend_from_slice(b.as_ref());
                a
            })
        } else if self.overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 1 {
            Vec::new()
        } else if self.overlay_network_index % NOTIFICATIONS_PROTOCOLS_PER_CHAIN == 2 {
            chain_config.role.scale_encoding().to_vec()
        } else {
            unreachable!()
        };

        self.libp2p
            .open_notifications_substream(
                self.connection_id,
                self.overlay_network_index,
                now,
                handshake,
            )
            .await;
    }
}

/// See [`Event::IdentifyRequestIn`].
#[must_use]
pub struct IdentifyRequestIn<'a, TNow> {
    service: &'a ChainNetwork<TNow>,
    connection_index: usize,
    id: libp2p::ConnectionId,
    substream_id: libp2p::connection::established::SubstreamId,
}

impl<'a, TNow> IdentifyRequestIn<'a, TNow>
where
    TNow: Clone + Add<Duration, Output = TNow> + Sub<TNow, Output = Duration> + Ord,
{
    /// Queue the response to send back. The future provided by [`ChainNetwork::read_write`] will
    /// automatically be woken up.
    ///
    /// Has no effect if the connection that sends the request no longer exists.
    pub async fn respond(self, agent_version: &str) {
        let response = {
            let guarded = self.service.guarded.lock().await;

            // The connection referred to by `self.id` might no longer exist anymore.
            // `self.connection_index` might no longer exist anymore or correspond to a different
            // connection. As such, if it exists, we need to compare its id with `self.id` to make
            // sure it still matches.
            let observed_addr = match guarded.connections.get(self.connection_index) {
                Some(c) => match &c.reached {
                    Some(r) if r.inner_id == self.id => &c.address,
                    _ => return,
                },
                None => return,
            };

            protocol::build_identify_response(protocol::IdentifyResponse {
                protocol_version: "/substrate/1.0", // TODO: same value as in Substrate
                agent_version,
                ed25519_public_key: self.service.libp2p.noise_key().libp2p_public_ed25519_key(),
                listen_addrs: iter::empty(), // TODO:
                observed_addr,
                protocols: self
                    .service
                    .libp2p
                    .request_response_protocols()
                    .filter(|p| p.inbound_allowed)
                    .map(|p| &p.name[..])
                    .chain(
                        self.service
                            .libp2p
                            .overlay_networks()
                            .map(|p| &p.protocol_name[..]),
                    ),
            })
            .fold(Vec::new(), |mut a, b| {
                a.extend_from_slice(b.as_ref());
                a
            })
        };

        let _ = self
            .service
            .libp2p
            .respond_in_request(self.id, self.substream_id, Ok(response))
            .await;
    }
}

impl<'a, TNow> fmt::Debug for IdentifyRequestIn<'a, TNow> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("IdentifyRequestIn").finish()
    }
}

/// Error during [`ChainNetwork::kademlia_discovery_round`].
#[derive(Debug, derive_more::Display)]
pub enum DiscoveryError {
    NoPeer,
    RequestFailed(libp2p::RequestError),
    DecodeError(kademlia::DecodeFindNodeResponseError),
}

/// Error returned by [`ChainNetwork::blocks_request`].
#[derive(Debug, derive_more::Display)]
pub enum BlocksRequestError {
    Request(libp2p::RequestError),
    Decode(protocol::DecodeBlockResponseError),
}

/// Error returned by [`ChainNetwork::storage_proof_request`].
#[derive(Debug, derive_more::Display)]
pub enum StorageProofRequestError {
    Request(libp2p::RequestError),
    Decode(protocol::DecodeStorageProofResponseError),
}

/// Error returned by [`ChainNetwork::call_proof_request`].
#[derive(Debug, derive_more::Display)]
pub enum CallProofRequestError {
    Request(libp2p::RequestError),
    Decode(protocol::DecodeCallProofResponseError),
}

/// Error returned by [`ChainNetwork::grandpa_warp_sync_request`].
#[derive(Debug, derive_more::Display)]
pub enum GrandpaWarpSyncRequestError {
    Request(libp2p::RequestError),
    Decode(protocol::DecodeGrandpaWarpSyncResponseError),
}

/// See [`Event::ProtocolError`].
#[derive(Debug, derive_more::Display)]
pub enum ProtocolError {
    /// Error while decoding the handshake of the block announces substream.
    BadBlockAnnouncesHandshake(protocol::BlockAnnouncesHandshakeDecodeError),
    /// Error while decoding a received block announce.
    BadBlockAnnounce(protocol::DecodeBlockAnnounceError),
    /// Error while decoding a received Grandpa notification.
    BadGrandpaNotification(protocol::DecodeGrandpaNotificationError),
}
