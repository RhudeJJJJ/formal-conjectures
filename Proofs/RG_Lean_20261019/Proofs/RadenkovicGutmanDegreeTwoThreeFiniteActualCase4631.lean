/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4631 : Family 10 := level10.get ⟨686,by decide⟩
def sourceMap4631 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4631 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4631_checked : acceptsGraphIso
    (source (graph core4631) (root 10) 2 2) DegreeTwoThreeSpectrum7330.graph sourceMap4631=true := by decide +kernel
theorem fusedMap4631_checked : acceptsGraphIso
    (fused (graph core4631) (root 10) 2 2) DegreeTwoThreeSpectrum5423.graph fusedMap4631=true := by decide +kernel
theorem certified4631 : Certified (graph core4631) (root 10) 2 2 :=
  of_native_maps core4631 DegreeTwoThreeSpectrum7330.graph DegreeTwoThreeSpectrum5423.graph
    sourceMap4631 fusedMap4631 sourceMap4631_checked fusedMap4631_checked
    DegreeTwoThreeFiniteComparisons.comparison4631
#print axioms sourceMap4631_checked
#print axioms fusedMap4631_checked
#print axioms certified4631
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
