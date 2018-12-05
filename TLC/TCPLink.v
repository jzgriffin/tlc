Require Import TLC.Byte.
Require Import TLC.IPLink.
Require Import TLC.Word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tcp.

  Definition tcp_port := word 16.

  Record tcp_socket :=
    TcpSocket {
      tcp_socket_address : ip_address;
      tcp_socket_port : tcp_port;
    }.

  Definition tcp_node := ip_address.
  Definition tcp_message := bytes.

  Definition tcp_connection := nat.

  (* From RFC 791 page 51 *)
  Definition tcp_ip_ttl := natToWord 8 60.
  Definition tcp_ip_service_type :=
    IpServiceType
      IpPrecedenceRoutine
      IpDelayNormal
      IpThroughputNormal
      IpReliabilityNormal.
  (* From RFC 790 page 6 *)
  Definition tcp_ip_protocol := natToWord 8 6.

  Inductive tcp_open_mode : Type :=
  | Active_tcp
  | Passive_tcp.

  Inductive tcp_request : Type :=
  | Open_tcp :
    tcp_node -> tcp_port -> option tcp_socket -> tcp_open_mode ->
    tcp_request
  | Close_tcp :
    tcp_node -> tcp_connection ->
    tcp_request
  | Send_tcp :
    tcp_node -> tcp_connection -> tcp_message ->
    tcp_request
  | Receive_tcp :
    tcp_node -> tcp_connection ->
    tcp_request
  | Abort_tcp :
    tcp_node -> tcp_connection ->
    tcp_request.

  Inductive tcp_indication : Type :=
  | OpenSuccess_tcp :
    tcp_node -> tcp_port -> option tcp_socket -> tcp_open_mode ->
    tcp_connection -> tcp_indication
  | OpenFailure_tcp :
    tcp_node -> tcp_port -> option tcp_socket -> tcp_open_mode ->
    tcp_indication
  | CloseSuccess_tcp :
    tcp_node -> tcp_connection ->
    tcp_indication
  | CloseFailure_tcp :
    tcp_node -> tcp_connection ->
    tcp_indication
  | SendSuccess_tcp :
    tcp_node -> tcp_connection -> tcp_message ->
    tcp_indication
  | SendFailure_tcp :
    tcp_node -> tcp_connection -> tcp_message ->
    tcp_indication
  | ReceiveSuccess_tcp :
    tcp_node -> tcp_connection ->
    tcp_message -> tcp_indication
  | ReceiveFailure_tcp :
    tcp_node -> tcp_connection ->
    tcp_indication
  | AbortSuccess_tcp :
    tcp_node -> tcp_connection ->
    tcp_indication
  | AbortFailure_tcp :
    tcp_node -> tcp_connection ->
    tcp_indication.

End tcp.
