/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4807 : Family 10 := level10.get ⟨1152,by decide⟩
def sourceMap4807 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4807 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4807_checked : acceptsGraphIso
    (source (graph core4807) (root 10) 2 2) DegreeTwoThreeSpectrum7238.graph sourceMap4807=true := by decide +kernel
theorem fusedMap4807_checked : acceptsGraphIso
    (fused (graph core4807) (root 10) 2 2) DegreeTwoThreeSpectrum6294.graph fusedMap4807=true := by decide +kernel
theorem certified4807 : Certified (graph core4807) (root 10) 2 2 :=
  of_native_maps core4807 DegreeTwoThreeSpectrum7238.graph DegreeTwoThreeSpectrum6294.graph
    sourceMap4807 fusedMap4807 sourceMap4807_checked fusedMap4807_checked
    DegreeTwoThreeFiniteComparisons.comparison4807
#print axioms sourceMap4807_checked
#print axioms fusedMap4807_checked
#print axioms certified4807
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
