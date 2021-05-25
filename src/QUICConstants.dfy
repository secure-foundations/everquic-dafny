include "NativeTypes.dfy"

module QUICConstants {
    import opened NativeTypes

    // frame const defintions
    const PADDING_TYPE :uint8 := 0x00
    const PING_TYPE :uint8 := 0x01
    const ACK_NON_ECN_TYPE : uint8 := 0x2
    const ACK_ECN_TYPE : uint8 := 0x3
    const RESET_STREAM_TYPE :uint8 := 0x04
    const STOP_SENDING_TYPE :uint8 := 0x05
    const CRYPTO_TYPE :uint8 := 0x06
    const NEW_TOKEN_TYPE :uint8 := 0x07

    const STREAM_TYPE_LOWER :uint8 := 0x08
    const STREAM_TYPE_UPPER :uint8 := 0x0f

    const MAX_DATA_TYPE :uint8 := 0x10
    const MAX_STREAM_DATA_TYPE :uint8 := 0x11
    const MAX_STREAMS_BIDI_TYPE: uint8 := 0x12
    const MAX_STREAMS_UNI_TYPE: uint8 := 0x13
    const DATA_BLOCKED_TYPE :uint8 := 0x14
    const STREAM_DATA_BLOCKED_TYPE :uint8 := 0x15
    const STREAMS_BLOCKED_BIDI_TYPE :uint8 := 0x16
    const STREAMS_BLOCKED_UNI_TYPE :uint8 := 0x17
    const NEW_CONNECTION_ID_TYPE :uint8 := 0x18
    const RETIRE_CONNECTION_ID_TYPE :uint8 := 0x19
    const PATH_CHALLENGE_TYPE :uint8 := 0x1a
    const PATH_RESPONSE_TYPE :uint8 := 0x1b
    const CONNECTION_CLOSE_QUIC_TYPE :uint8 := 0x1c
    const CONNECTION_CLOSE_APP_TYPE :uint8 := 0x1d

    const DEFAULT_MAX_STREAM_DATA : uint62 := 0x1000000000;

    // packet const defintions

    const INITIAL_TYPE :uint2 := 0x0
    const ZERORTT_TYPE :uint2 := 0x1
    const HANDSHAKE_TYPE :uint2 := 0x2
    const RETRY_TYPE :uint2 := 0x3

    const quicVersion :uint32 := 0xff000018
    const MAX_OUTGOING_ACKS :uint32 := 4096

    const maxoutgoing_acks :uint32 := 4096

    // Indicies into the connection.keys array
    const epochIndexInitial:byte := 0
    const epochIndex0RTT:byte := 1
    const epochIndexHandshake:byte := 2
    const epochIndex1RTT:byte := 3

    const stateless_reset_token_length:uint64 := 16;

    // transport params
    const ORIGINAL_CONNECTION_ID :uint16 := 0
    const IDLE_TIMEOUT :uint16 := 1
    const STATELESS_RESET_TOKEN :uint16 := 2
    const MAX_PACKET_SIZE :uint16 := 3
    const INITIAL_MAX_DATA :uint16 := 4
    const INITIAL_MAX_STREAM_DATA_BIDI_LOCAL :uint16 := 5
    const INITIAL_MAX_STREAM_DATA_BIDI_REMOTE :uint16 := 6
    const INITIAL_MAX_STREAM_DATA_UNI :uint16 := 7
    const INITIAL_MAX_STREAMS_BIDI :uint16 := 8
    const INITIAL_MAX_STREAMS_UNI :uint16 := 9
    const ACK_DELAY_EXPONENT :uint16 := 10
    const MAX_ACK_DELAY :uint16 := 11
    const DISABLE_ACTIVE_MIGRATION :uint16 := 12
    const PREFERRED_ADDRESS :uint16 := 13
    const ACTIVE_CONNECTION_ID_LIMIT :uint16 := 14

    const PN_BYTES :uint32 := 4;
    const PAYLOAD_LENGTH_BYTES :uint32 := 8;
    const ENCODED_PN_LENGTH :uint2 := 3;
    const AUTH_TAG_LENGTH :uint32 := 16
    const INITIAL_PACKET_MIN_LENGTH : uint32:= 1300;
    const LONG_HEADER_MASK :uint8 := 0x80;

    const PREPARE_SUCCESS :uint8 := 0x0;
    const PREPARE_ERROR_OTHER :uint8 := 0x1;
    const PREPARE_ERROR_CLOSED :uint8 := 0x2;
}
