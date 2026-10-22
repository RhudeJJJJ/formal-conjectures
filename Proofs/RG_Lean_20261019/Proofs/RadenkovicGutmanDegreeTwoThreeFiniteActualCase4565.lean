/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4565 : Family 10 := level10.get ⟨488,by decide⟩
def sourceMap4565 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4565 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 2 2 v)
theorem sourceMap4565_checked : acceptsGraphIso
    (source (graph core4565) (root 10) 2 2) DegreeTwoThreeSpectrum7016.graph sourceMap4565=true := by decide +kernel
theorem fusedMap4565_checked : acceptsGraphIso
    (fused (graph core4565) (root 10) 2 2) DegreeTwoThreeSpectrum5953.graph fusedMap4565=true := by decide +kernel
theorem certified4565 : Certified (graph core4565) (root 10) 2 2 :=
  of_native_maps core4565 DegreeTwoThreeSpectrum7016.graph DegreeTwoThreeSpectrum5953.graph
    sourceMap4565 fusedMap4565 sourceMap4565_checked fusedMap4565_checked
    DegreeTwoThreeFiniteComparisons.comparison4565
#print axioms sourceMap4565_checked
#print axioms fusedMap4565_checked
#print axioms certified4565
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
