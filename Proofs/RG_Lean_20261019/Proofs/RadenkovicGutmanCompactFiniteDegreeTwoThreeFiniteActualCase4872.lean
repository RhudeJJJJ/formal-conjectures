/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4872 : Family 10 := level10.get ⟨1308,by decide⟩
def sourceMap4872 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4872 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4872_checked : acceptsGraphIso
    (source (graph core4872) (root 10) 2 2) DegreeTwoThreeSpectrum7390.graph sourceMap4872=true := by decide +kernel
theorem fusedMap4872_checked : acceptsGraphIso
    (fused (graph core4872) (root 10) 2 2) DegreeTwoThreeSpectrum6605.graph fusedMap4872=true := by decide +kernel
theorem certified4872 : Certified (graph core4872) (root 10) 2 2 :=
  of_native_maps core4872 DegreeTwoThreeSpectrum7390.graph DegreeTwoThreeSpectrum6605.graph
    sourceMap4872 fusedMap4872 sourceMap4872_checked fusedMap4872_checked
    DegreeTwoThreeFiniteComparisons.comparison4872
#print axioms sourceMap4872_checked
#print axioms fusedMap4872_checked
#print axioms certified4872
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
