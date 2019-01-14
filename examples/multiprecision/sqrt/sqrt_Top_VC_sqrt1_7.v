(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Reals.R_sqrt.
Require Reals.Rtrigo_def.
Require Reals.Rpower.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require int.Abs.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require int.Power.
Require real.Real.
Require real.RealInfix.
Require real.FromInt.
Require real.Truncate.
Require real.Square.
Require real.ExpLog.
Require real.PowerReal.
Require map.Map.
Require map.Const.

Require Import Reals.

Axiom uint64 : Type.
Parameter uint64_WhyType : WhyType uint64.
Existing Instance uint64_WhyType.

Parameter uint64'int: uint64 -> Z.

Axiom uint64'axiom :
  forall (i:uint64),
  (0%Z <= (uint64'int i))%Z /\ ((uint64'int i) <= 18446744073709551615%Z)%Z.

(* Why3 assumption *)
Definition in_bounds (n:Z) : Prop :=
  (0%Z <= n)%Z /\ (n <= 18446744073709551615%Z)%Z.

Axiom to_int_in_bounds : forall (n:uint64), in_bounds (uint64'int n).

Axiom extensionality :
  forall (x:uint64) (y:uint64), ((uint64'int x) = (uint64'int y)) -> (x = y).

Parameter zero_unsigned: uint64.

Axiom zero_unsigned_is_zero : ((uint64'int zero_unsigned) = 0%Z).

Axiom array : forall (a:Type), Type.
Parameter array_WhyType :
  forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.

Parameter elts: forall {a:Type} {a_WT:WhyType a}, (array a) -> Z -> a.

Parameter length: forall {a:Type} {a_WT:WhyType a}, (array a) -> Z.

Axiom array'invariant :
  forall {a:Type} {a_WT:WhyType a},
  forall (self:array a), (0%Z <= (length self))%Z.

(* Why3 assumption *)
Definition mixfix_lbrb {a:Type} {a_WT:WhyType a} (a1:array a) (i:Z) : a :=
  (elts a1) i.

Parameter mixfix_lblsmnrb:
  forall {a:Type} {a_WT:WhyType a}, (array a) -> Z -> a -> array a.

Axiom mixfix_lblsmnrb_spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (i:Z) (v:a),
  ((length (mixfix_lblsmnrb a1 i v)) = (length a1)) /\
  ((elts (mixfix_lblsmnrb a1 i v)) = (map.Map.set (elts a1) i v)).

Parameter make: forall {a:Type} {a_WT:WhyType a}, Z -> a -> array a.

Axiom make_spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (n:Z) (v:a), (0%Z <= n)%Z ->
  (forall (i:Z), ((0%Z <= i)%Z /\ (i < n)%Z) ->
   ((mixfix_lbrb (make n v) i) = v)) /\
  ((length (make n v)) = n).

(* Why3 assumption *)
Definition map_eq_sub {a:Type} {a_WT:WhyType a} (a1:Z -> a) (a2:Z -> a) 
    (l:Z) (u:Z) : Prop :=
  forall (i:Z), ((l <= i)%Z /\ (i < u)%Z) -> ((a1 i) = (a2 i)).

(* Why3 assumption *)
Definition map_eq_sub_shift {a:Type} {a_WT:WhyType a} (x:Z -> a) (y:Z -> a)
    (xi:Z) (yi:Z) (sz:Z) : Prop :=
  forall (i:Z), ((0%Z <= i)%Z /\ (i < sz)%Z) ->
  ((x (xi + i)%Z) = (y (yi + i)%Z)).

Axiom map_eq_shift :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:Z -> a) (y:Z -> a) (xi:Z) (yi:Z) (sz:Z) (k:Z),
  (map_eq_sub_shift x y xi yi sz) -> ((0%Z <= k)%Z /\ (k < sz)%Z) ->
  ((x (xi + k)%Z) = (y (yi + k)%Z)).

Axiom map_eq_shift_zero :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:Z -> a) (y:Z -> a) (n:Z) (m:Z),
  (map_eq_sub_shift x y n n (m - n)%Z) -> map_eq_sub x y n m.

Axiom int32 : Type.
Parameter int32_WhyType : WhyType int32.
Existing Instance int32_WhyType.

Parameter int32'int: int32 -> Z.

Axiom int32'axiom :
  forall (i:int32),
  ((-2147483648%Z)%Z <= (int32'int i))%Z /\ ((int32'int i) <= 2147483647%Z)%Z.

(* Why3 assumption *)
Definition in_bounds1 (n:Z) : Prop :=
  ((-2147483648%Z)%Z <= n)%Z /\ (n <= 2147483647%Z)%Z.

Axiom to_int_in_bounds1 : forall (n:int32), in_bounds1 (int32'int n).

Axiom extensionality1 :
  forall (x:int32) (y:int32), ((int32'int x) = (int32'int y)) -> (x = y).

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Arguments mk_ref {a}.

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:ref a) : a :=
  match v with
  | mk_ref x => x
  end.

Axiom int64 : Type.
Parameter int64_WhyType : WhyType int64.
Existing Instance int64_WhyType.

Parameter int64'int: int64 -> Z.

Axiom int64'axiom :
  forall (i:int64),
  ((-9223372036854775808%Z)%Z <= (int64'int i))%Z /\
  ((int64'int i) <= 9223372036854775807%Z)%Z.

(* Why3 assumption *)
Definition in_bounds2 (n:Z) : Prop :=
  ((-9223372036854775808%Z)%Z <= n)%Z /\ (n <= 9223372036854775807%Z)%Z.

Axiom to_int_in_bounds2 : forall (n:int64), in_bounds2 (int64'int n).

Axiom extensionality2 :
  forall (x:int64) (y:int64), ((int64'int x) = (int64'int y)) -> (x = y).

(* Why3 assumption *)
Definition in_bounds3 (n:Z) : Prop :=
  (0%Z <= n)%Z /\ (n <= 18446744073709551615%Z)%Z.

Axiom to_int_in_bounds3 : forall (n:uint64), in_bounds3 (uint64'int n).

Axiom extensionality3 :
  forall (x:uint64) (y:uint64), ((uint64'int x) = (uint64'int y)) -> (x = y).

Parameter zero_unsigned1: uint64.

Axiom zero_unsigned_is_zero1 : ((uint64'int zero_unsigned1) = 0%Z).

Parameter uint64_max: uint64.

Axiom uint64_max_def : ((uint64'int uint64_max) = 18446744073709551615%Z).

Parameter is_msb_set: uint64 -> Prop.

Axiom is_msb_set_spec :
  forall (x:uint64),
  (is_msb_set x) <-> (18446744073709551615%Z < (2%Z * (uint64'int x))%Z)%Z.

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter max: Z.

Parameter to_int: t -> Z.

(* Why3 assumption *)
Definition in_bounds4 (n:Z) : Prop := (0%Z <= n)%Z /\ (n <= max)%Z.

Axiom to_int_in_bounds4 : forall (n:t), in_bounds4 (to_int n).

Axiom extensionality4 :
  forall (x:t) (y:t), ((to_int x) = (to_int y)) -> (x = y).

Parameter zero_unsigned2: t.

Axiom zero_unsigned_is_zero2 : ((to_int zero_unsigned2) = 0%Z).

Parameter radix: Z.

Axiom radix_def : (radix = (max + 1%Z)%Z).

Axiom uint32 : Type.
Parameter uint32_WhyType : WhyType uint32.
Existing Instance uint32_WhyType.

Parameter uint32'int: uint32 -> Z.

Axiom uint32'axiom :
  forall (i:uint32),
  (0%Z <= (uint32'int i))%Z /\ ((uint32'int i) <= 4294967295%Z)%Z.

(* Why3 assumption *)
Definition in_bounds5 (n:Z) : Prop := (0%Z <= n)%Z /\ (n <= 4294967295%Z)%Z.

Axiom to_int_in_bounds5 : forall (n:uint32), in_bounds5 (uint32'int n).

Axiom extensionality5 :
  forall (x:uint32) (y:uint32), ((uint32'int x) = (uint32'int y)) -> (x = y).

Parameter zero_unsigned3: uint32.

Axiom zero_unsigned_is_zero3 : ((uint32'int zero_unsigned3) = 0%Z).

Parameter is_msb_set1: uint32 -> Prop.

Axiom is_msb_set_spec1 :
  forall (x:uint32),
  (is_msb_set1 x) <-> (4294967295%Z < (2%Z * (uint32'int x))%Z)%Z.

(* Why3 assumption *)
Definition in_us_bounds (n:Z) : Prop :=
  (0%Z <= n)%Z /\ (n <= 4294967295%Z)%Z.

(* Why3 assumption *)
Definition in_bounds6 (n:Z) : Prop :=
  ((-2147483648%Z)%Z <= n)%Z /\ (n <= 2147483647%Z)%Z.

Axiom zone : Type.
Parameter zone_WhyType : WhyType zone.
Existing Instance zone_WhyType.

Parameter null_zone: zone.

Axiom ptr : forall (a:Type), Type.
Parameter ptr_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ptr a).
Existing Instance ptr_WhyType.

Parameter data: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> array a.

Parameter offset: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> Z.

Parameter min: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> Z.

Parameter max1: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> Z.

Parameter zone1: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> zone.

(* Why3 assumption *)
Definition plength {a:Type} {a_WT:WhyType a} (p:ptr a) : Z :=
  length (data p).

(* Why3 assumption *)
Definition pelts {a:Type} {a_WT:WhyType a} (p:ptr a) : Z -> a :=
  elts (data p).

Parameter is_not_null: forall {a:Type} {a_WT:WhyType a}, (ptr a) -> Prop.

Axiom is_not_null_spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (p:ptr a), (is_not_null p) <-> ~ ((zone1 p) = null_zone).

(* Why3 assumption *)
Definition valid_ptr_shift {a:Type} {a_WT:WhyType a} (p:ptr a) (i:Z) : Prop :=
  ((min p) <= ((offset p) + i)%Z)%Z /\ (((offset p) + i)%Z < (max1 p))%Z.

(* Why3 assumption *)
Definition valid {a:Type} {a_WT:WhyType a} (p:ptr a) (sz:Z) : Prop :=
  (in_bounds6 sz) /\
  ((0%Z <= sz)%Z /\
   (((0%Z <= (min p))%Z /\ ((min p) <= (offset p))%Z) /\
    ((((offset p) + sz)%Z <= (max1 p))%Z /\ ((max1 p) <= (plength p))%Z))).

Axiom valid_itv_to_shift :
  forall {a:Type} {a_WT:WhyType a},
  forall (p:ptr a) (sz:Z), (valid p sz) -> forall (i:Z),
  ((0%Z <= i)%Z /\ (i < sz)%Z) -> valid_ptr_shift p i.

(* Why3 assumption *)
Definition limb := uint64.

(* Why3 assumption *)
Definition t1 := ptr uint64.

Axiom limb_max_bound : (1%Z <= 18446744073709551615%Z)%Z.

Axiom prod_compat_strict_r :
  forall (a:Z) (b:Z) (c:Z), ((0%Z <= a)%Z /\ (a < b)%Z) -> (0%Z < c)%Z ->
  ((c * a)%Z < (c * b)%Z)%Z.

Axiom prod_compat_r :
  forall (a:Z) (b:Z) (c:Z), ((0%Z <= a)%Z /\ (a <= b)%Z) -> (0%Z <= c)%Z ->
  ((c * a)%Z <= (c * b)%Z)%Z.

Parameter value_sub: (Z -> uint64) -> Z -> Z -> Z.

Axiom value_sub_def :
  forall (x:Z -> uint64) (n:Z) (m:Z),
  ((n < m)%Z ->
   ((value_sub x n m) =
    ((uint64'int (x n)) +
     ((18446744073709551615%Z + 1%Z)%Z * (value_sub x (n + 1%Z)%Z m))%Z)%Z)) /\
  (~ (n < m)%Z -> ((value_sub x n m) = 0%Z)).

Axiom value_sub_frame :
  forall (x:Z -> uint64) (y:Z -> uint64) (n:Z) (m:Z), (map_eq_sub x y n m) ->
  ((value_sub x n m) = (value_sub y n m)).

Axiom value_sub_frame_shift :
  forall (x:Z -> uint64) (y:Z -> uint64) (xi:Z) (yi:Z) (sz:Z),
  (map_eq_sub_shift x y xi yi sz) ->
  ((value_sub x xi (xi + sz)%Z) = (value_sub y yi (yi + sz)%Z)).

Axiom value_sub_tail :
  forall (x:Z -> uint64) (n:Z) (m:Z), (n <= m)%Z ->
  ((value_sub x n (m + 1%Z)%Z) =
   ((value_sub x n m) +
    ((uint64'int (x m)) *
     (int.Power.power (18446744073709551615%Z + 1%Z)%Z (m - n)%Z))%Z)%Z).

Axiom value_sub_concat :
  forall (x:Z -> uint64) (n:Z) (m:Z) (l:Z), ((n <= m)%Z /\ (m <= l)%Z) ->
  ((value_sub x n l) =
   ((value_sub x n m) +
    ((value_sub x m l) *
     (int.Power.power (18446744073709551615%Z + 1%Z)%Z (m - n)%Z))%Z)%Z).

Axiom value_sub_head :
  forall (x:Z -> uint64) (n:Z) (m:Z), (n < m)%Z ->
  ((value_sub x n m) =
   ((uint64'int (x n)) +
    ((18446744073709551615%Z + 1%Z)%Z * (value_sub x (n + 1%Z)%Z m))%Z)%Z).

Axiom value_sub_update :
  forall (x:Z -> uint64) (i:Z) (n:Z) (m:Z) (v:uint64),
  ((n <= i)%Z /\ (i < m)%Z) ->
  ((value_sub (map.Map.set x i v) n m) =
   ((value_sub x n m) +
    ((int.Power.power (18446744073709551615%Z + 1%Z)%Z (i - n)%Z) *
     ((uint64'int v) - (uint64'int (x i)))%Z)%Z)%Z).

Axiom value_zero :
  forall (x:Z -> uint64) (n:Z) (m:Z),
  (map_eq_sub x (map.Const.const zero_unsigned1 : Z -> uint64) n m) ->
  ((value_sub x n m) = 0%Z).

Axiom value_sub_update_no_change :
  forall (x:Z -> uint64) (i:Z) (n:Z) (m:Z) (v:uint64), (n <= m)%Z ->
  ((i < n)%Z \/ (m <= i)%Z) ->
  ((value_sub x n m) = (value_sub (map.Map.set x i v) n m)).

Axiom value_sub_shift_no_change :
  forall (x:Z -> uint64) (ofs:Z) (i:Z) (sz:Z) (v:uint64),
  ((i < 0%Z)%Z \/ (sz <= i)%Z) -> (0%Z <= sz)%Z ->
  ((value_sub x ofs (ofs + sz)%Z) =
   (value_sub (map.Map.set x (ofs + i)%Z v) ofs (ofs + sz)%Z)).

Axiom value_sub_lower_bound :
  forall (x:Z -> uint64) (x1:Z) (x2:Z), (0%Z <= (value_sub x x1 x2))%Z.

Axiom value_sub_upper_bound :
  forall (x:Z -> uint64) (x1:Z) (x2:Z), (x1 <= x2)%Z ->
  ((value_sub x x1 x2) <
   (int.Power.power (18446744073709551615%Z + 1%Z)%Z (x2 - x1)%Z))%Z.

Axiom value_sub_lower_bound_tight :
  forall (x:Z -> uint64) (x1:Z) (x2:Z), (x1 < x2)%Z ->
  (((int.Power.power (18446744073709551615%Z + 1%Z)%Z ((x2 - x1)%Z - 1%Z)%Z)
    * (uint64'int (x (x2 - 1%Z)%Z)))%Z
   <= (value_sub x x1 x2))%Z.

Axiom value_sub_upper_bound_tight :
  forall (x:Z -> uint64) (x1:Z) (x2:Z), (x1 < x2)%Z ->
  ((value_sub x x1 x2) <
   ((int.Power.power (18446744073709551615%Z + 1%Z)%Z ((x2 - x1)%Z - 1%Z)%Z)
    * ((uint64'int (x (x2 - 1%Z)%Z)) + 1%Z)%Z)%Z)%Z.

(* Why3 assumption *)
Definition value (x:ptr uint64) (sz:Z) : Z :=
  value_sub (pelts x) (offset x) ((offset x) + sz)%Z.

Axiom value_concat :
  forall (x:ptr uint64) (n:int32) (m:int32),
  ((0%Z <= (int32'int n))%Z /\ ((int32'int n) <= (int32'int m))%Z) ->
  ((value x (int32'int m)) =
   ((value x (int32'int n)) +
    ((int.Power.power (18446744073709551615%Z + 1%Z)%Z (int32'int n)) *
     (value_sub (pelts x) ((offset x) + (int32'int n))%Z
      ((offset x) + (int32'int m))%Z))%Z)%Z).

(* Why3 assumption *)
Definition pow2 (k:Z) : R := (Reals.Rpower.Rpower 2%R (BuiltIn.IZR k)).

(* Why3 assumption *)
Definition trunc_at (x:R) (k:Z) : R :=
  ((BuiltIn.IZR (real.Truncate.floor (x * (pow2 (-k)%Z))%R)) * (pow2 k))%R.

Axiom fxp : Type.
Parameter fxp_WhyType : WhyType fxp.
Existing Instance fxp_WhyType.

Parameter ival: fxp -> uint64.

Parameter rval: fxp -> R.

Parameter iexp: fxp -> Z.

Axiom fxp'invariant :
  forall (self:fxp),
  ((rval self) = (trunc_at (rval self) (iexp self))) /\
  ((uint64'int (ival self)) =
   (int.EuclideanDivision.mod1
    (real.Truncate.floor ((rval self) * (pow2 (-(iexp self))%Z))%R)
    (18446744073709551615%Z + 1%Z)%Z)).

Parameter a0: uint64.

Axiom H : (4611686018427387904%Z <= (uint64'int a0))%Z.

Parameter a: fxp.

Axiom H1 : ((ival a) = a0).

Axiom H2 : ((rval a) = ((BuiltIn.IZR (uint64'int a0)) * (pow2 (-64%Z)%Z))%R).

Axiom H3 : ((iexp a) = (-64%Z)%Z).

Axiom H4 :
  ((025 / 100)%R <= (rval a))%R /\
  ((rval a) <= (18446744073709551615 / 18446744073709551616)%R)%R.

Axiom H5 : (0%R < (rval a))%R.

Parameter x0: fxp.

Axiom H6 : ((iexp x0) = (-8%Z)%Z).

Axiom H7 : (256%Z <= (uint64'int (ival x0)))%Z.

Axiom H8 : ((uint64'int (ival x0)) <= 511%Z)%Z.

Axiom H9 : (1%R <= (rval x0))%R.

Axiom H10 : ((rval x0) <= 2%R)%R.

Axiom H11 :
  let rsa := (1%R / (Reals.R_sqrt.sqrt (rval a)))%R in
  let e0 := (((rval x0) - rsa)%R / rsa)%R in
  ((-(000281 / 100000)%R)%R <= e0)%R /\ (e0 <= (0002655 / 1000000)%R)%R.

Parameter a1: fxp.

Axiom H12 : ((rval a1) = (trunc_at (rval a) ((iexp a) + 31%Z)%Z)).

Axiom H13 : ((iexp a1) = ((iexp a) + 31%Z)%Z).

Parameter o: fxp.

Axiom H14 : ((rval o) = ((rval x0) * (rval x0))%R).

Axiom H15 : ((iexp o) = ((iexp x0) + (iexp x0))%Z).

Parameter o1: fxp.

Axiom H16 : ((rval o1) = ((rval o) * (rval a1))%R).

Axiom H17 : ((iexp o1) = ((iexp o) + (iexp a1))%Z).

Parameter o2: fxp.

Parameter rliteral: uint64.

Axiom rliteral_axiom : ((uint64'int rliteral) = 196608%Z).

Axiom H18 : ((ival o2) = rliteral).

Axiom H19 : ((rval o2) = ((BuiltIn.IZR 196608%Z) * (pow2 (-49%Z)%Z))%R).

Axiom H20 : ((iexp o2) = (-49%Z)%Z).

Parameter o3: fxp.

Parameter rliteral1: uint64.

Axiom rliteral_axiom1 : ((uint64'int rliteral1) = 562949953421312%Z).

Axiom H21 : ((ival o3) = rliteral1).

Axiom H22 :
  ((rval o3) = ((BuiltIn.IZR 562949953421312%Z) * (pow2 (-49%Z)%Z))%R).

Axiom H23 : ((iexp o3) = (-49%Z)%Z).

Parameter o4: fxp.

Axiom H24 : ((rval o4) = ((rval o3) - (rval o2))%R).

Axiom H25 : ((iexp o4) = (iexp o3)).

Parameter t1': fxp.

Axiom H26 : ((rval t1') = ((rval o4) - (rval o1))%R).

Axiom H27 : ((iexp t1') = (iexp o4)).

Parameter t11: fxp.

Axiom H28 : ((rval t11) = (trunc_at (rval t1') ((iexp t1') + 16%Z)%Z)).

Axiom H29 : ((iexp t11) = ((iexp t1') + 16%Z)%Z).

Parameter o5: fxp.

Axiom H30 : ((rval o5) = ((rval x0) * (rval t11))%R).

Axiom H31 : ((iexp o5) = ((iexp x0) + (iexp t11))%Z).

Parameter o6: fxp.

Axiom H32 :
  ((rval o6) =
   (trunc_at ((rval o5) * (pow2 (-1%Z)%Z))%R (((iexp o5) + 18%Z)%Z - 1%Z)%Z)).

Axiom H33 : ((iexp o6) = (((iexp o5) + 18%Z)%Z - 1%Z)%Z).

Parameter o7: fxp.

Axiom H34 : ((rval o7) = (rval x0)).

Axiom H35 : ((iexp o7) = ((iexp x0) - 16%Z)%Z).

Parameter x1: fxp.

Axiom H36 : ((rval x1) = ((rval o7) + (rval o6))%R).

Axiom H37 : ((iexp x1) = (iexp o7)).

Axiom H38 :
  (((((rval x0) + (((rval x0) * (rval t1'))%R * (05 / 10)%R)%R)%R -
     (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R
    / (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R
   =
   ((-(05 / 10)%R)%R *
    ((((((rval x0) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
        (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R
       *
       (((rval x0) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
        (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R
      *
      (3%R +
       (((rval x0) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
        (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R)%R
     +
     ((1%R +
       (((rval x0) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
        (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R
      *
      ((3 / 8589934592)%R +
       (((1%R +
          (((rval x0) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
           (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R
         *
         (1%R +
          (((rval x0) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
           (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R)%R
        * (((rval a1) - (rval a))%R / (rval a))%R)%R)%R)%R)%R)%R).

Parameter a2: fxp.

Axiom H39 : ((rval a2) = (trunc_at (rval a) ((iexp a) + 24%Z)%Z)).

Axiom H40 : ((iexp a2) = ((iexp a) + 24%Z)%Z).

Parameter a3: fxp.

Axiom H41 : ((rval a3) = (rval a)).

Axiom H42 : ((iexp a3) = ((iexp a) - 14%Z)%Z).

Parameter u1: fxp.

Axiom H43 : ((rval u1) = ((rval x1) * (rval a2))%R).

Axiom H44 : ((iexp u1) = ((iexp x1) + (iexp a2))%Z).

Axiom H45 :
  (((1%R / (Reals.R_sqrt.sqrt (rval a)))%R * (rval a))%R =
   (Reals.R_sqrt.sqrt (rval a))).

Parameter u2: fxp.

Axiom H46 : ((rval u2) = (trunc_at (rval u1) ((iexp u1) + 25%Z)%Z)).

Axiom H47 : ((iexp u2) = ((iexp u1) + 25%Z)%Z).

(* Why3 goal *)
Theorem VC_sqrt1 :
  (((rval a) - (((rval x1) * (rval a))%R * ((rval x1) * (rval a))%R)%R)%R =
   (-(((rval a) *
     (((rval x1) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
      (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R
    *
    (2%R +
     (((rval x1) - (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R /
      (1%R / (Reals.R_sqrt.sqrt (rval a)))%R)%R)%R))%R).
Proof.
set (sa := sqrt (rval a)).
replace (rval a) with (sa^2)%R.
field.
apply Rgt_not_eq, sqrt_lt_R0, H5.
rewrite <- Rsqr_pow2.
apply Rsqr_sqrt, Rlt_le, H5.
Qed.

