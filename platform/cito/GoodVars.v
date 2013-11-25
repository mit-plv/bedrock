Require Import ReservedNames.
Require Import List String.

Set Implicit Arguments.

Local Open Scope string.
Local Open Scope list.

Definition good_vars vars temp_vars := 
  NoDup ("rp" :: STACK_CAPACITY :: vars ++ temp_vars).