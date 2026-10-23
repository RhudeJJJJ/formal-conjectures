/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
module
public import Proofs.RadenkovicGutmanPublicAnchor000Interface

public section
namespace Gebendorfer.RadenkovicGutman.PublicAnchor000Consumer
open scoped Classical
noncomputable section

theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1)
    (hN : Fintype.card V+9+9+2≤52) :
    ((3949369501170259056731373497378897/32624163332060752803334972325527552 : ℚ) : ℝ)≤
      ActualFusionIntegral.normalizedIntegral G u 9 9 ((51/26 : ℚ) : ℝ) :=
  PublicAnchor000Interface.actual_bound G u hd hN

#print axioms actual_bound
end
end Gebendorfer.RadenkovicGutman.PublicAnchor000Consumer
