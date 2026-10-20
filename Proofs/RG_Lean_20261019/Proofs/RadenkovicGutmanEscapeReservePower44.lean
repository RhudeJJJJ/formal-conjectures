/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedIntegerHybrid
/-! One exact power coefficient; no positivity or full tensor closure is asserted. -/
namespace Gebendorfer.RadenkovicGutman.EscapeReservePower44
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def data : NestedInteger.Poly 3 := [[[],[],[],[],[],[],[],[],[0,0,0,0,0,0,0,0,39003751353608260131225600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]]]
theorem data_length : data.length = 1 := by decide +kernel
#print axioms data_length
end Gebendorfer.RadenkovicGutman.EscapeReservePower44
