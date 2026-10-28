/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5009 : Family 10 := level10.get ⟨1639,by decide⟩
def sourceMap5009 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5009 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5009_checked : acceptsGraphIso
    (source (graph core5009) (root 10) 2 2) DegreeTwoThreeSpectrum7610.graph sourceMap5009=true := by decide +kernel
theorem fusedMap5009_checked : acceptsGraphIso
    (fused (graph core5009) (root 10) 2 2) DegreeTwoThreeSpectrum6214.graph fusedMap5009=true := by decide +kernel
theorem certified5009 : Certified (graph core5009) (root 10) 2 2 :=
  of_native_maps core5009 DegreeTwoThreeSpectrum7610.graph DegreeTwoThreeSpectrum6214.graph
    sourceMap5009 fusedMap5009 sourceMap5009_checked fusedMap5009_checked
    DegreeTwoThreeFiniteComparisons.comparison5009
#print axioms sourceMap5009_checked
#print axioms fusedMap5009_checked
#print axioms certified5009
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
