/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4533 : Family 10 := level10.get ⟨400,by decide⟩
def sourceMap4533 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4533 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4533_checked : acceptsGraphIso
    (source (graph core4533) (root 10) 2 2) DegreeTwoThreeSpectrum6830.graph sourceMap4533=true := by decide +kernel
theorem fusedMap4533_checked : acceptsGraphIso
    (fused (graph core4533) (root 10) 2 2) DegreeTwoThreeSpectrum5755.graph fusedMap4533=true := by decide +kernel
theorem certified4533 : Certified (graph core4533) (root 10) 2 2 :=
  of_native_maps core4533 DegreeTwoThreeSpectrum6830.graph DegreeTwoThreeSpectrum5755.graph
    sourceMap4533 fusedMap4533 sourceMap4533_checked fusedMap4533_checked
    DegreeTwoThreeFiniteComparisons.comparison4533
#print axioms sourceMap4533_checked
#print axioms fusedMap4533_checked
#print axioms certified4533
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
