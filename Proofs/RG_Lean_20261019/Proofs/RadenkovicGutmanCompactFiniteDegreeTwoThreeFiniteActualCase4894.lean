/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4894 : Family 10 := level10.get ⟨1358,by decide⟩
def sourceMap4894 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4894 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4894_checked : acceptsGraphIso
    (source (graph core4894) (root 10) 2 2) DegreeTwoThreeSpectrum7439.graph sourceMap4894=true := by decide +kernel
theorem fusedMap4894_checked : acceptsGraphIso
    (fused (graph core4894) (root 10) 2 2) DegreeTwoThreeSpectrum6694.graph fusedMap4894=true := by decide +kernel
theorem certified4894 : Certified (graph core4894) (root 10) 2 2 :=
  of_native_maps core4894 DegreeTwoThreeSpectrum7439.graph DegreeTwoThreeSpectrum6694.graph
    sourceMap4894 fusedMap4894 sourceMap4894_checked fusedMap4894_checked
    DegreeTwoThreeFiniteComparisons.comparison4894
#print axioms sourceMap4894_checked
#print axioms fusedMap4894_checked
#print axioms certified4894
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
