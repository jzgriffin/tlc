Require Import TLC.Word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ip.

  Definition ip_address := word 32.

  Inductive ip_precedence :=
  | IpPrecedenceNetworkControl
  | IpPrecedenceInternetworkControl
  | IpPrecedenceCriticEcp
  | IpPrecedenceFlashOverride
  | IpPrecedenceFlash
  | IpPrecedenceImmediate
  | IpPrecedencePriority
  | IpPrecedenceRoutine.

  Definition ip_precedence_to_nat (p : ip_precedence) :=
    match p with
    | IpPrecedenceNetworkControl => 7
    | IpPrecedenceInternetworkControl => 6
    | IpPrecedenceCriticEcp => 5
    | IpPrecedenceFlashOverride => 4
    | IpPrecedenceFlash => 3
    | IpPrecedenceImmediate => 2
    | IpPrecedencePriority => 1
    | IpPrecedenceRoutine => 0
    end.

  Definition ip_precedence_to_word (p : ip_precedence) : word 3 :=
    natToWord _ (ip_precedence_to_nat p).

  Inductive ip_delay :=
  | IpDelayNormal
  | IpDelayLow.

  Definition ip_delay_to_nat (d : ip_delay) :=
    match d with
    | IpDelayNormal => 0
    | IpDelayLow => 1
    end.

  Definition ip_delay_to_word (d : ip_delay) : word 1 :=
    natToWord _ (ip_delay_to_nat d).

  Inductive ip_throughput :=
  | IpThroughputNormal
  | IpThroughputHigh.

  Definition ip_throughput_to_nat (t : ip_throughput) :=
    match t with
    | IpThroughputNormal => 0
    | IpThroughputHigh => 1
    end.

  Definition ip_throughput_to_word (t : ip_throughput) : word 1 :=
    natToWord _ (ip_throughput_to_nat t).

  Inductive ip_reliability :=
  | IpReliabilityNormal
  | IpReliabilityHigh.

  Definition ip_reliability_to_nat (r : ip_reliability) :=
    match r with
    | IpReliabilityNormal => 0
    | IpReliabilityHigh => 1
    end.

  Definition ip_reliability_to_word (r : ip_reliability) : word 1 :=
    natToWord _ (ip_reliability_to_nat r).

  Record ip_service_type :=
    IpServiceType {
      ip_service_type_precedence : ip_precedence;
      ip_service_type_delay : ip_delay;
      ip_service_type_throughput : ip_throughput;
      ip_service_type_reliability : ip_reliability;
    }.

  Definition ip_service_type_to_word (st : ip_service_type) : word 8 :=
    let p := ip_service_type_precedence st in
    let pw := ip_precedence_to_word p in
    let d := ip_service_type_delay st in
    let dw := ip_delay_to_word d in
    let t := ip_service_type_throughput st in
    let tw := ip_throughput_to_word t in
    let r := ip_service_type_reliability st in
    let rw := ip_reliability_to_word r in
    combine (wzero 2) (combine rw (combine tw (combine dw pw))).

End ip.
