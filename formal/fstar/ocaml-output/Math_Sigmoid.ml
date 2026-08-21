open Prims
type scaled = (Prims.int * Prims.nat)
let (work_scale : Prims.nat) = (Prims.of_int (24))
let (work_pow10 : Prims.int) = Math_Expr.pow10 work_scale
let (to_work : scaled -> Prims.int) =
  fun s ->
    let uu___ = s in
    match uu___ with
    | (m, sc) ->
        if sc <= work_scale
        then m * (Math_Expr.pow10 (work_scale - sc))
        else
          (let d = Math_Expr.pow10 (sc - work_scale) in
           if d = Prims.int_zero then m else m / d)
let (from_work : Prims.int -> Prims.nat -> scaled) =
  fun wp ->
    fun scale ->
      if scale >= work_scale
      then ((wp * (Math_Expr.pow10 (scale - work_scale))), scale)
      else
        (let d = Math_Expr.pow10 (work_scale - scale) in
         if d = Prims.int_zero then (wp, scale) else ((wp / d), scale))
let (wp_from_int : Prims.int -> Prims.int) = fun n -> n * work_pow10
let (wp_add : Prims.int -> Prims.int -> Prims.int) = fun a -> fun b -> a + b
let (wp_sub : Prims.int -> Prims.int -> Prims.int) = fun a -> fun b -> a - b
let (wp_neg : Prims.int -> Prims.int) = fun a -> Prims.int_zero - a
let (wp_mul : Prims.int -> Prims.int -> Prims.int) =
  fun a ->
    fun b ->
      if work_pow10 = Prims.int_zero
      then Prims.int_zero
      else (a * b) / work_pow10
let (wp_div : Prims.int -> Prims.int -> Prims.int) =
  fun a ->
    fun b ->
      if b = Prims.int_zero then Prims.int_zero else (a * work_pow10) / b
let rec (wp_ipow : Prims.int -> Prims.nat -> Prims.int) =
  fun base ->
    fun e ->
      if e = Prims.int_zero
      then wp_from_int Prims.int_one
      else wp_mul base (wp_ipow base (e - Prims.int_one))
let rec (taylor_sum :
  Prims.int -> Prims.nat -> Prims.nat -> Prims.int -> Prims.int) =
  fun r ->
    fun term_idx ->
      fun fuel ->
        fun acc ->
          if fuel = Prims.int_zero
          then acc
          else
            (let rk = wp_ipow r term_idx in
             let factk = wp_from_int (Math_Expr.ifact term_idx) in
             let term = wp_div rk factk in
             taylor_sum r (term_idx + Prims.int_one) (fuel - Prims.int_one)
               (wp_add acc term))
let (reduction_shift : Prims.nat) = (Prims.of_int (10))
let (taylor_terms : Prims.nat) = (Prims.of_int (13))
let (output_scale : Prims.nat) = (Prims.of_int (9))
let (exp_small : Prims.int -> Prims.int) =
  fun r ->
    taylor_sum r Prims.int_zero taylor_terms (wp_from_int Prims.int_zero)
let rec (square_repeat : Prims.int -> Prims.nat -> Prims.int) =
  fun v ->
    fun times ->
      if times = Prims.int_zero
      then v
      else square_repeat (wp_mul v v) (times - Prims.int_one)
let (exp_approx_wp : Prims.int -> Prims.int) =
  fun x_wp ->
    let divisor =
      wp_from_int (Math_Expr.ipow (Prims.of_int (2)) reduction_shift) in
    let r = wp_div x_wp divisor in
    let base = exp_small r in square_repeat base reduction_shift
let (exp_approx : scaled -> scaled) =
  fun x ->
    let x_wp = to_work x in
    let y_wp = exp_approx_wp x_wp in from_work y_wp output_scale
let rec (sigmoid_points_wp :
  Prims.int ->
    Prims.int ->
      Prims.int ->
        Prims.int ->
          Prims.int ->
            Prims.nat -> Prims.nat -> (Prims.int * Prims.int) Prims.list)
  =
  fun k_wp ->
    fun x0_wp ->
      fun l_wp ->
        fun xmin_wp ->
          fun step_wp ->
            fun i ->
              fun fuel ->
                if fuel = Prims.int_zero
                then []
                else
                  (let x_wp = wp_add xmin_wp (wp_mul (wp_from_int i) step_wp) in
                   let neg_k_dx = wp_neg (wp_mul k_wp (wp_sub x_wp x0_wp)) in
                   let e_wp = exp_approx_wp neg_k_dx in
                   let denom_wp = wp_add (wp_from_int Prims.int_one) e_wp in
                   let y_wp = wp_div l_wp denom_wp in (x_wp, y_wp) ::
                     (sigmoid_points_wp k_wp x0_wp l_wp xmin_wp step_wp
                        (i + Prims.int_one) (fuel - Prims.int_one)))
let (sigmoid_points :
  scaled ->
    scaled ->
      scaled -> scaled -> scaled -> Prims.nat -> (scaled * scaled) Prims.list)
  =
  fun k ->
    fun x0 ->
      fun l ->
        fun xmin ->
          fun xmax ->
            fun n ->
              let k_wp = to_work k in
              let x0_wp = to_work x0 in
              let l_wp = to_work l in
              let xmin_wp = to_work xmin in
              let xmax_wp = to_work xmax in
              let step_wp =
                if n = Prims.int_zero
                then wp_from_int Prims.int_zero
                else wp_div (wp_sub xmax_wp xmin_wp) (wp_from_int n) in
              let pts =
                sigmoid_points_wp k_wp x0_wp l_wp xmin_wp step_wp
                  Prims.int_zero (n + Prims.int_one) in
              FStar_List_Tot_Base.map
                (fun p ->
                   ((from_work (FStar_Pervasives_Native.fst p) output_scale),
                     (from_work (FStar_Pervasives_Native.snd p) output_scale)))
                pts
