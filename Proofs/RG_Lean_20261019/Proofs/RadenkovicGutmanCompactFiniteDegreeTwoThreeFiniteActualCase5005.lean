/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5005 : Family 10 := level10.get ⟨1632,by decide⟩
def sourceMap5005 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap5005 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5005_checked : acceptsGraphIso
    (source (graph core5005) (root 10) 2 2) DegreeTwoThreeSpectrum7606.graph sourceMap5005=true := by decide +kernel
theorem fusedMap5005_checked : acceptsGraphIso
    (fused (graph core5005) (root 10) 2 2) DegreeTwoThreeSpectrum6197.graph fusedMap5005=true := by decide +kernel
theorem certified5005 : Certified (graph core5005) (root 10) 2 2 :=
  of_native_maps core5005 DegreeTwoThreeSpectrum7606.graph DegreeTwoThreeSpectrum6197.graph
    sourceMap5005 fusedMap5005 sourceMap5005_checked fusedMap5005_checked
    DegreeTwoThreeFiniteComparisons.comparison5005
#print axioms sourceMap5005_checked
#print axioms fusedMap5005_checked
#print axioms certified5005
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
