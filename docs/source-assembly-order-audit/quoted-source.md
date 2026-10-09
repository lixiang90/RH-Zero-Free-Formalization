# Exact source excerpts for the read-only integration audit

These are source excerpts, not a new Lean verification. Full raw snapshots and original pinned Git blobs are bound in metadata.json.

## OAI/NumberTheory/DirichletL/Detector/FinalAssemblyData.lean

Actual raw SHA256: `e4ed7337985e8b5843727f0884472dd98f3c04934fef839f4e184125cf8c57fa`; original Git blob: `ebc462f5678b6c9dafd55ee8a434d1538d814790`.

### `structure SourceData` (actual lines 12–35)

```lean
12: local notation "O" => HeckeFamily.O
13: 
14: structure SourceData {Δ : ℝ} (D : HighData Δ) where
15:   S : Finset (Ideal O)
16:   exclusions : SourceExclusions S
17:   maximal : ∀P∈S,P.IsMaximal
18:   first : FirstTail (4*D.e) S
19:   w : ℝ→ℝ
20:   W : SchwartzMap ℝ ℂ
21:   smooth : ContDiff ℝ ∞ w
22:   compact : HasCompactSupport w
23:   support : Function.support w⊆Set.Ioo 1 2
24:   positive_support : tsupport w⊆Set.Ioi 0
25:   bounded : ∀x,0≤w x ∧ w x≤1
26:   nonzero : w≠0
27:   complex_eq : ∀x,W x=(w x:ℂ)
28:   complex_nonzero : W≠0
29:   complex_support : Function.support W⊆Set.Icc 1 2
30:   real : ∀x,(W x).im=0
31:   nonnegative : ∀x,0≤(W x).re
32: 
33: theorem exists_source_data {Δ : ℝ} (D : HighData Δ) : Nonempty (SourceData D) := by
34:   obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
35:   obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
```

## OAI/NumberTheory/DirichletL/ParametersFixedSource.lean

Actual raw SHA256: `6d17586f6573f6ffcbc1343af5e7b27f5cc19824a0ada96a8bdff0b0adc2a1b8`; original Git blob: `d7dc90c32ac1ceafb542191ac782e9ed4e13e9a9`.

### `exists_fixed_source` (actual lines 24–47)

```lean
24:       twoIdeal_maximal.isPrime
25: 
26: theorem exists_fixed_source (e : ℝ) (he : 0<e)
27:     (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
28:     ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
29:       FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal) := by
30:   obtain ⟨S,hsub,hS,hfirst⟩ := exists_both_source_exclusions (4*e) (by positivity)
31:     (S₀∪fixedBadPrimes)
32:     (fun P hP => (Finset.mem_union.mp hP).elim (hS₀ P) (fixed_bad_primes_prime P))
33:     Finset.subset_union_right
34:   refine ⟨S,Finset.subset_union_left.trans hsub,hS,hfirst,?_⟩
35:   intro P hP
36:   exact (Ideal.isPrime_of_prime (hS.prime P hP)).isMaximal (hS.prime P hP).ne_zero
37: 
38: theorem exists_fixed_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
39:     ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
40:     Function.support w⊆Set.Ioo 1 2 ∧ tsupport w⊆Set.Ioi 0 ∧
41:     (∀x,0≤w x ∧ w x≤1) ∧ w≠0 ∧ (∀x,W x=(w x:ℂ)) ∧ W≠0 ∧
42:     Function.support W⊆Set.Icc 1 2 ∧
43:     (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
44:   obtain ⟨w,W,hw,hc,hs,hb,hv,hn,he,hWn,hWs,hr,hp⟩ := exists_probe_window
45:   refine ⟨w,W,hw,hc,hs,?_,hb,hn,he,hWn,hWs,hr,hp⟩
46:   have hcl : tsupport w⊆Set.Icc 1 2 :=
47:     closure_minimal (hs.trans Set.Ioo_subset_Icc_self) isClosed_Icc
```

## OAI/NumberTheory/DirichletL/ParametersHighData.lean

Actual raw SHA256: `4bbf9a79f4a7caa8ba443c1e5f6dbacfd6821d59d993270443b46f2d212b0691`; original Git blob: `c565dc0a72c7da9a2706cdd835e69a39e8c0dc14`.

### `exists_high_data` (actual lines 50–73)

```lean
50:     4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t
51: 
52: theorem exists_high_data (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
53:   obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
54:   obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
55:     exists_physical_slot_lengths (1/200) (7/8) t t (by norm_num) (by norm_num) ht ht
56:   obtain ⟨allowance,ha,hbud⟩ := hallow N
57:   let small := min allowance (t/((N:ℝ)+2000))
58:   have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
59:   have hsa : small≤allowance := min_le_left _ _
60:   have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
61:   have hst0 : small≤t/2000 := hst.trans
62:     (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
63:   let ellMin := (7/8:ℝ)*rmin
64:   have hmin : 0<ellMin := mul_pos (by norm_num) hr
65:   obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
66:     hdet,hphase,_,_,_,_,_⟩ :=
67:     exists_detector_scales t rmin t (1/200) t ellMin small 0
68:       ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
69:   let eps := small/2
70:   have heps : 0<eps := by dsimp [eps];positivity
71:   have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
72:   have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
73:   have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
```

## OAI/NumberTheory/DirichletL/ParametersDetectorScales.lean

Actual raw SHA256: `1c2157f609c66a2437ee2fdf643f0d675ecbb35cf176daee2e5387e0c3435cc7`; original Git blob: `fcc6a547cd6eb0fb5da4e72e3ce926549415a7bf`.

### `exists_detector_scales` (actual lines 6–29)

```lean
6: namespace SevenEighths.Parameters
7: 
8: theorem exists_detector_scales (R rmin mesh dmin loss ellMin allowance J : ℝ)
9:     (hR : 0≤R) (hr : 0<rmin) (hm : 0<mesh) (hd : 0<dmin)
10:     (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
11:     ∃ε e κ cost τ : ℝ,
12:       0<ε ∧ ε≤1/1000 ∧ ε<rmin*mesh ∧ ε≤allowance ∧
13:       0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
14:       0<κ ∧ κ≤1 ∧ 0<cost ∧
15:       12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
16:       8*e*R+κ≤ε ∧
17:       0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
18:       2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
19:   let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
20:   have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
21:   have hεa : ε≤allowance/2 := min_le_left _ _
22:   have hεr : ε≤rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
23:   have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
24:   let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
25:   have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
26:   have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
27:   have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
28:   have heR : 0≤e*R := mul_nonneg he.le hR
29:   have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
```

## OAI/NumberTheory/DirichletL/PrimeRows/FirstTail.lean

Actual raw SHA256: `be3d26d2846b67df0a208d6050600a9a8cea312fc8b052cb1c0763fe8369e7ee`; original Git blob: `8806252442ce00087a3fd007dabcc17e56ac996a`.

### `firstPrimeDefectBound` (actual lines 11–34)

```lean
11: local notation "O" => HeckeFamily.O
12: 
13: def firstPrimeDefectBound (eps : ℝ) (P : PrimeIdeal) : ℝ :=
14:   240*(P.val.absNorm : ℝ)^(-1-min eps (1/50:ℝ))
15: 
16: theorem firstPrimeDefectBound_nonneg (eps : ℝ) (P : PrimeIdeal) :
17:     0≤firstPrimeDefectBound eps P := by unfold firstPrimeDefectBound; positivity
18: 
19: theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
20:     Summable (firstPrimeDefectBound eps) := by
21:   have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
22:     simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
23:     have hm : 0<min eps (1/50:ℝ) := lt_min heps (by norm_num)
24:     linarith
25:   have h := (CubicEisenstein.fullIdealWeight_summable_norm
26:     (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
27:     (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
28:   apply (h.mul_left 240).congr
29:   intro P
30:   change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
31:   unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
32:   simp only [P.property.ne_zero,ite_false]
33:   rw [Complex.norm_natCast_cpow_of_pos
34:     (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
```

### `structure FirstTail` (actual lines 37–60)

```lean
37:   ring
38: 
39: structure FirstTail (eps : ℝ) (S : Finset (Ideal O)) : Prop where
40:   positive : 0<eps
41:   norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤P.val.absNorm
42:   small : (∑' P : {P : PrimeIdeal // P.val∉S},firstPrimeDefectBound eps P.val)≤1/6
43: 
44: theorem FirstTail.summable {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S) :
45:     Summable (fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val) :=
46:   (firstPrimeDefectBound_summable eps h.positive).subtype _
47: 
48: theorem FirstTail.half {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S)
49:     (P : {P : PrimeIdeal // P.val∉S}) : firstPrimeDefectBound eps P.val≤1/2 := by
50:   have hh := Summable.le_tsum h.summable P (fun Q _=>firstPrimeDefectBound_nonneg eps Q.val)
51:   linarith [h.small]
52: 
53: theorem exists_first_cutoff (eps : ℝ) (heps : 0<eps) :
54:     ∃N : ℕ,4≤N ∧ ∀S : Finset (Ideal O),
55:       (∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S) → FirstTail eps S := by
56:   have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (firstPrimeDefectBound eps))).2
57:     (1/6) (by norm_num)
58:   obtain ⟨F,hF⟩ := ht.exists
59:   let N := max 4 (F.sup (fun P=>P.val.absNorm))
60:   refine ⟨N,le_max_left _ _,?_⟩
```

### `exists_both_source_exclusions` (actual lines 79–102)

```lean
79:       ((firstPrimeDefectBound_summable eps heps).subtype _)
80: 
81: theorem exists_both_source_exclusions (eps : ℝ) (heps : 0<eps)
82:     (S₀ : Finset (Ideal O)) (hp : ∀P∈S₀,Prime P)
83:     (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S₀) :
84:     ∃S : Finset (Ideal O),S₀⊆S ∧ SourceExclusions S ∧ FirstTail eps S := by
85:   obtain ⟨N₁,hN₁,hcut₁⟩ := exists_uniform_global_cutoff
86:   obtain ⟨N₂,hN₂,hcut₂⟩ := exists_first_cutoff eps heps
87:   let N := max N₁ N₂
88:   let S := S₀∪smallPrimeSet N
89:   have hpS : ∀P∈S,Prime P := by
90:     intro P hP
91:     rcases Finset.mem_union.mp hP with hP|hP
92:     · exact hp P hP
93:     · exact (Finset.mem_filter.mp hP).2
94:   have hcut : ∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S := by
95:     intro P hP
96:     exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
97:   refine ⟨S,Finset.subset_union_left,⟨hpS,hbad.trans Finset.subset_union_left,?_⟩,?_⟩
98:   · exact hcut₁ S (fun P hP=>hcut P (hP.trans (le_max_left _ _)))
99:   · exact hcut₂ S (fun P hP=>hcut P (hP.trans (le_max_right _ _)))
100: 
101: end SevenEighths.ProbeHighRowFamily
102: 
```

## OAI/NumberTheory/DirichletL/Detector/SourceExclusions.lean

Actual raw SHA256: `7ce136a63d2478f75c876bc7404717a426b97829132b9c634647009a4cb8d650`; original Git blob: `438bef0305ffa1afef7198d392a664c32afdac80`.

### `structure SourceExclusions` (actual lines 22–45)

```lean
22:   exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))
23: 
24: structure SourceExclusions (S : Finset Id) : Prop where
25:   prime : ∀P∈S,Prime P
26:   bad : fixedBadPrimes⊆S
27:   tail : CorrectionTail S
28: 
29: theorem exists_source_exclusions (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
30:     (hbad : fixedBadPrimes⊆S₀) :
31:     ∃S : Finset Id,S₀⊆S ∧ SourceExclusions S := by
32:   obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
33:   refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
34:   constructor
35:   · intro P hP
36:     rcases Finset.mem_union.mp hP with hP|hP
37:     · exact hp P hP
38:     · exact (Finset.mem_filter.mp hP).2
39:   · exact hbad.trans Finset.subset_union_left
40:   · apply hcut
41:     intro P hP
42:     exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
43: 
44: theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
45:     (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
```

## OAI/NumberTheory/DirichletL/Detector/GlobalCorrection.lean

Actual raw SHA256: `e884072eed927e5260281e7f6065262b7d3209d2825b52836c9571841630fef9`; original Git blob: `81bd73f1f3df61d4768969fd677b97f2dde64452`.

### `globalPrimeDefectBound` (actual lines 13–36)

```lean
13: local notation "Id" => Ideal O
14: 
15: def globalPrimeDefectBound (P : PrimeIdeal) : ℝ :=
16:   240*(Ideal.absNorm P.val:ℝ)^(-(17/10:ℝ))
17: 
18: def globalClosedCorrection (η : HeckeFamily.Character) (S : Finset Id) (x w z : ℂ) : ℂ :=
19:   ∏' P : {P : PrimeIdeal // P.val∉S},idealClosedCorrection η P.val x w z
20: 
21: lemma globalPrimeDefectBound_nonneg (P : PrimeIdeal) : 0≤globalPrimeDefectBound P := by
22:   unfold globalPrimeDefectBound
23:   positivity
24: 
25: lemma globalPrimeDefectBound_summable : Summable globalPrimeDefectBound := by
26:   have h := (CubicEisenstein.fullIdealWeight_summable_norm ((17/10:ℝ):ℂ) (by norm_num)).comp_injective
27:     (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
28:   apply (h.mul_left 240).congr
29:   intro P
30:   change 240*‖CubicEisenstein.fullIdealWeight ((17/10:ℝ):ℂ) P.val‖=globalPrimeDefectBound P
31:   unfold globalPrimeDefectBound CubicEisenstein.fullIdealWeight
32:   simp only [P.property.ne_zero,ite_false]
33:   rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
34:   norm_num
35: 
36: structure CorrectionTail (S : Finset Id) : Prop where
```

### `exists_uniform_global_cutoff` (actual lines 138–161)

```lean
138:   rfl
139: 
140: theorem exists_uniform_global_cutoff :
141:     ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
142:       (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → CorrectionTail S := by
143:   have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero globalPrimeDefectBound)).2 (1/6) (by norm_num)
144:   obtain ⟨F,hF⟩ := ht.exists
145:   let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
146:   refine ⟨N,le_max_left _ _,?_⟩
147:   intro S hS
148:   let T := {P : PrimeIdeal // P.val∉S}
149:   have hnot (P : T) : P.val∉F := by
150:     intro hm
151:     exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
152:   let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
153:   have hi : Function.Injective inc := by
154:     intro P Q h
155:     exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
156:   constructor
157:   · intro P hP
158:     have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
159:     exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
160:   · apply le_trans ?_ hF.le
161:     exact Summable.tsum_le_tsum_of_inj inc hi
```

## OAI/NumberTheory/DirichletL/Energy/WidthRanges.lean

Actual raw SHA256: `9ab32adcd244a3f1662df6bdcc1263b94afbe2819fc435097743b01b40f43a4d`; original Git blob: `4763f92c5a0c439262841b1bbd839809dd44ae4b`.

### `def fineMesh` (actual lines 16–39)

```lean
16: def sourceCap (M B L:ℝ)(n:ℕ):ℝ:=10*(range M B L n+M+B+1)
17: def finalSourceCap (M B L ε:ℝ):ℝ:=sourceCap M B L (count M ε)
18: def fineMesh (M B L κ ε:ℝ):ℝ:=mesh M (finalSourceCap M B L ε) κ ε
19: 
20: lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤range M B L n:=by
21:   induction n with
22:   | zero=>exact zero_le_one.trans (le_max_left _ _)
23:   | succ n ih=>simp only [range,step];positivity
24: 
25: lemma range_mono (M B L:ℝ)(hM:0≤M)(hB:0≤B):Monotone (range M B L):=by
26:   apply monotone_nat_of_le_succ
27:   intro n
28:   have hh:=range_nonneg M B L hM hB n
29:   simp only [range,step]
30:   linarith
31: 
32: lemma range_original (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):L≤range M B L n:=by
33:   exact (le_max_right (1:ℝ) L).trans (range_mono M B L hM hB (Nat.zero_le n))
34: 
35: lemma step_admits (M B L rho d e:ℝ)(hM:0≤M)(hB:0≤B)(hL:0≤L)
36:     (hrho:rho≤1)(hd:d≤1)(he:e≤1):
37:     L≤step M B L ∧ M+B+rho/100+1≤step M B L ∧
38:     max L (M+B+2*d)+1≤step M B L ∧
39:     2*L+e≤step M B L ∧
```

### `fineMesh_pos` (actual lines 82–97)

```lean
82:   positivity
83: 
84: lemma fineMesh_pos (M B L κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
85:     0<fineMesh M B L κ ε:=by
86:   exact (bounds M (finalSourceCap M B L ε) κ ε hM
87:     (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.2.1
88: 
89: lemma support_step (a b:ℝ)(ha:0<a)(n:ℕ):
90:     0<lower a b (n+1) ∧ lower a b (n+1)=lower a b n/max 1 b:=
91:   ⟨lower_pos a b ha _,rfl⟩
92: 
93: end SevenEighths.CenteredMomentEnergyWidthRanges
94: 
95: end
96: 
97: end OAI
```

