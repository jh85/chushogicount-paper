import ChuShogi.SummaryCode
import ChuShogi.GroupedFiles

/-! Extending complete natural-weight table semantics to rational test weights.
Equality of only supplied entries is not used: indicator tests cover every key.
-/
namespace ChuShogi.RationalTable
variable {S : Type} [DecidableEq S]

def integral (t : WeightedDP.Table S) (f : S → ℚ) : ℚ := (t.map fun e => (e.2 : ℚ)*f e.1).sum

omit [DecidableEq S] in
theorem integral_nil (f : S → ℚ) : integral [] f = 0 := rfl

omit [DecidableEq S] in
theorem integral_cons (e : S × Nat) (t : WeightedDP.Table S) (f : S → ℚ) :
    integral (e::t) f = (e.2 : ℚ)*f e.1+integral t f := rfl

theorem integral_insert (s : S) (w : Nat) (t : WeightedDP.Table S) (f : S → ℚ) :
    integral (WeightedDP.insert s w t) f = (w : ℚ)*f s+integral t f := by
  induction t with
  | nil => simp [WeightedDP.insert,integral]
  | cons e t ih =>
    rcases e with ⟨r,n⟩
    simp only [WeightedDP.insert]
    split
    · rename_i h; subst r; simp [integral,Nat.cast_add,add_mul,add_assoc]
    · simp only [integral_cons,ih]
      ring

theorem integral_convolve (merge : S → S → S) (a b : WeightedDP.Table S) (f : S → ℚ) :
    integral (WeightedDP.convolve merge a b) f =
      integral a (fun s => integral b (fun v => f (merge s v))) := by
  have inner (e : S × Nat) (out : WeightedDP.Table S) :
      integral (b.foldr (fun v out => WeightedDP.insert (merge e.1 v.1) (e.2*v.2) out) out) f =
        (e.2 : ℚ)*integral b (fun v => f (merge e.1 v))+integral out f := by
    induction b with
    | nil => simp [integral]
    | cons v b ih =>
      simp only [List.foldr_cons]
      rw [integral_insert,ih]
      simp only [integral_cons,Nat.cast_mul]
      ring
  induction a with
  | nil => rfl
  | cons e a ih =>
    change integral (b.foldr _ (WeightedDP.convolve merge a b)) f = _
    rw [inner,ih,integral_cons]

omit [DecidableEq S] in
theorem integral_mul (t : WeightedDP.Table S) (w : ℚ) (f : S → ℚ) :
    integral t (fun s => w*f s) = w*integral t f := by
  induction t with
  | nil => simp [integral]
  | cons e t ih => simp only [integral_cons,ih]; ring

omit [DecidableEq S] in
theorem integral_add (t : WeightedDP.Table S) (f g : S → ℚ) :
    integral t (fun s => f s+g s) = integral t f+integral t g := by
  induction t with
  | nil => simp [integral]
  | cons e t ih => simp only [integral_cons,ih]; ring

omit [DecidableEq S] in
theorem integral_exchange {T : Type} (a : WeightedDP.Table S) (b : WeightedDP.Table T) (f : S → T → ℚ) :
    integral a (fun s => integral b (f s)) = integral b (fun t => integral a (fun s => f s t)) := by
  induction a with
  | nil => simp [integral]
  | cons e a ih => simp only [integral_cons,integral_add,integral_mul,ih]

omit [DecidableEq S] in
theorem integral_map_key {T : Type} (t : WeightedDP.Table S) (p : S → T) (f : T → ℚ) :
    integral (t.map fun e => (p e.1,e.2)) f = integral t (fun s => f (p s)) := by
  unfold integral
  rw [List.map_map]
  rfl

omit [DecidableEq S] in
theorem integral_append (a b : WeightedDP.Table S) (f : S → ℚ) : integral (a++b) f = integral a f+integral b f := by
  simp only [integral,List.map_append,List.sum_append]

omit [DecidableEq S] in
theorem integral_flatMap (xs : List A) (make : A → WeightedDP.Table S) (f : S → ℚ) :
    integral (xs.flatMap make) f = (xs.map fun x => integral (make x) f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,integral_append,List.map_cons,List.sum_cons,ih]

omit [DecidableEq S] in
theorem integral_congr (t : WeightedDP.Table S) (f g : S → ℚ)
    (h : ∀ e ∈ t, f e.1=g e.1) : integral t f = integral t g := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  rw [h e he]

theorem integral_histogram (xs : List A) (feature : A → S) (f : S → ℚ) :
    integral (WeightedDP.histogram xs feature) f = (xs.map fun x => f (feature x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change integral (WeightedDP.insert (feature x) 1 (WeightedDP.histogram xs feature)) f = _
    rw [integral_insert,ih]
    simp

omit [DecidableEq S] in
theorem integral_cast (t : WeightedDP.Table S) (f : S → Nat) :
    integral t (fun s => (f s : ℚ)) = (WeightedDP.integral t f : ℚ) := by
  induction t with
  | nil => rfl
  | cons e t ih => simp only [integral_cons,WeightedDP.integral_cons,Nat.cast_add,Nat.cast_mul,ih]

theorem sum_lookup (t : WeightedDP.Table S) (keys : Finset S) (f : S → ℚ)
    (hk : ∀ e ∈ t, e.1 ∈ keys) :
    integral t f = ∑ s ∈ keys, (WeightedDP.lookup t s : ℚ)*f s := by
  induction t with
  | nil => simp [integral,WeightedDP.lookup]
  | cons e t ih =>
    have he := hk e (by simp)
    have ht : ∀ v ∈ t, v.1 ∈ keys := fun v hv => hk v (by simp [hv])
    rw [integral_cons,ih ht]
    have hm (s : S) : (WeightedDP.lookup (e::t) s : ℚ)*f s =
        (if e.1=s then (e.2 : ℚ)*f s else 0)+(WeightedDP.lookup t s : ℚ)*f s := by
      rw [HashAggregation.lookup_cons]
      by_cases h : e.1=s <;> simp [h,add_mul]
    simp_rw [hm]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [he]

/-- Complete equality of natural-weight integrals implies equality for every
rational completion function, without assuming integrality of the function. -/
theorem ext (t u : WeightedDP.Table S)
    (h : ∀ f : S → Nat, WeightedDP.integral t f = WeightedDP.integral u f) (f : S → ℚ) :
    integral t f = integral u f := by
  let keys := ((t++u).map Prod.fst).toFinset
  have ht : ∀ e ∈ t, e.1 ∈ keys := by
    intro e he
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨e,List.mem_append.mpr (.inl he),rfl⟩
  have hu : ∀ e ∈ u, e.1 ∈ keys := by
    intro e he
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨e,List.mem_append.mpr (.inr he),rfl⟩
  rw [sum_lookup t keys f ht,sum_lookup u keys f hu]
  apply Finset.sum_congr rfl
  intro s _
  have he : WeightedDP.lookup t s = WeightedDP.lookup u s := h (fun r => if r=s then 1 else 0)
  rw [he]

theorem dp_integral (initial : S) (merge : S → S → S) (feature : A → S)
    (files : List (List A)) (f : S → ℚ) : integral (WeightedDP.dp initial merge feature files) f =
      ((WeightedDP.tuples files).map fun us => f (WeightedDP.summary initial merge feature us)).sum := by
  have hn (g : S → Nat) : WeightedDP.integral (WeightedDP.dp initial merge feature files) g =
      WeightedDP.integral (WeightedDP.histogram (WeightedDP.tuples files)
        (WeightedDP.summary initial merge feature)) g := by
    rw [WeightedDP.dp_integral,WeightedDP.integral_histogram]
  rw [ext _ _ hn f,integral_histogram]

theorem hash_dp [BEq S] [Hashable S] [LawfulBEq S] (initial : S) (merge : S → S → S)
    (feature : A → S) (files : List (List A)) (f : S → ℚ) :
    integral (HashAggregation.dp initial merge feature files) f =
      integral (WeightedDP.dp initial merge feature files) f :=
  ext _ _ (fun g => HashAggregation.dp_integral initial merge feature files g) f

theorem hash_convolve [BEq S] [Hashable S] [LawfulBEq S] (merge : S → S → S)
    (a b : WeightedDP.Table S) (f : S → ℚ) :
    integral (HashAggregation.convolve merge a b) f = integral (WeightedDP.convolve merge a b) f :=
  ext _ _ (fun g => HashAggregation.convolve_integral merge a b g) f

theorem hash_accumulate [BEq S] [Hashable S] [LawfulBEq S] (t : WeightedDP.Table S) (f : S → ℚ) :
    integral (HashAggregation.accumulate t).toList f = integral t f :=
  ext _ _ (HashAggregation.accumulate_integral t) f

theorem hash_group (files : List (List ConcreteDP.Local)) (f : ConcreteDP.Summary → ℚ) :
    integral (SummaryCode.groupTable files) f =
      integral (WeightedDP.dp ConcreteDP.zero ConcreteDP.add CompactSummary.compactFeature files) f :=
  ext _ _ (SummaryCode.group_integral files) f

theorem grouped (f : ConcreteDP.Summary → ℚ) :
    integral GroupedFiles.groupedTable f = integral CompactSummary.compactTable f :=
  ext _ _ GroupedFiles.grouped_integral f

end ChuShogi.RationalTable
