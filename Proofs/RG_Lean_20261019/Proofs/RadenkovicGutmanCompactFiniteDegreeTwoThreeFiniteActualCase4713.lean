/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4713 : Family 10 := level10.get ⟨912,by decide⟩
def sourceMap4713 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4713 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4713_checked : acceptsGraphIso
    (source (graph core4713) (root 10) 2 2) DegreeTwoThreeSpectrum7481.graph sourceMap4713=true := by decide +kernel
theorem fusedMap4713_checked : acceptsGraphIso
    (fused (graph core4713) (root 10) 2 2) DegreeTwoThreeSpectrum5783.graph fusedMap4713=true := by decide +kernel
theorem certified4713 : Certified (graph core4713) (root 10) 2 2 :=
  of_native_maps core4713 DegreeTwoThreeSpectrum7481.graph DegreeTwoThreeSpectrum5783.graph
    sourceMap4713 fusedMap4713 sourceMap4713_checked fusedMap4713_checked
    DegreeTwoThreeFiniteComparisons.comparison4713
#print axioms sourceMap4713_checked
#print axioms fusedMap4713_checked
#print axioms certified4713
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
