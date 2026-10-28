/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5041 : Family 10 := level10.get ⟨1740,by decide⟩
def sourceMap5041 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5041 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5041_checked : acceptsGraphIso
    (source (graph core5041) (root 10) 2 2) DegreeTwoThreeSpectrum7642.graph sourceMap5041=true := by decide +kernel
theorem fusedMap5041_checked : acceptsGraphIso
    (fused (graph core5041) (root 10) 2 2) DegreeTwoThreeSpectrum6586.graph fusedMap5041=true := by decide +kernel
theorem certified5041 : Certified (graph core5041) (root 10) 2 2 :=
  of_native_maps core5041 DegreeTwoThreeSpectrum7642.graph DegreeTwoThreeSpectrum6586.graph
    sourceMap5041 fusedMap5041 sourceMap5041_checked fusedMap5041_checked
    DegreeTwoThreeFiniteComparisons.comparison5041
#print axioms sourceMap5041_checked
#print axioms fusedMap5041_checked
#print axioms certified5041
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
