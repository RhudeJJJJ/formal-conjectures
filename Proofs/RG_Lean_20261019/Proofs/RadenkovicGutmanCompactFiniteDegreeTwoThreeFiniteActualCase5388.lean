/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5388 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap5388 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5388 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5388_checked : acceptsGraphIso
    (source (graph core5388) (root 6) 4 4) DegreeTwoThreeSpectrum7047.graph sourceMap5388=true := by decide +kernel
theorem fusedMap5388_checked : acceptsGraphIso
    (fused (graph core5388) (root 6) 4 4) DegreeTwoThreeSpectrum4975.graph fusedMap5388=true := by decide +kernel
theorem certified5388 : Certified (graph core5388) (root 6) 4 4 :=
  of_native_maps core5388 DegreeTwoThreeSpectrum7047.graph DegreeTwoThreeSpectrum4975.graph
    sourceMap5388 fusedMap5388 sourceMap5388_checked fusedMap5388_checked
    DegreeTwoThreeFiniteComparisons.comparison5388
#print axioms sourceMap5388_checked
#print axioms fusedMap5388_checked
#print axioms certified5388
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
