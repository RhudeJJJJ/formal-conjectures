/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4635 : Family 10 := level10.get ⟨698,by decide⟩
def sourceMap4635 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4635 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4635_checked : acceptsGraphIso
    (source (graph core4635) (root 10) 2 2) DegreeTwoThreeSpectrum7349.graph sourceMap4635=true := by decide +kernel
theorem fusedMap4635_checked : acceptsGraphIso
    (fused (graph core4635) (root 10) 2 2) DegreeTwoThreeSpectrum5436.graph fusedMap4635=true := by decide +kernel
theorem certified4635 : Certified (graph core4635) (root 10) 2 2 :=
  of_native_maps core4635 DegreeTwoThreeSpectrum7349.graph DegreeTwoThreeSpectrum5436.graph
    sourceMap4635 fusedMap4635 sourceMap4635_checked fusedMap4635_checked
    DegreeTwoThreeFiniteComparisons.comparison4635
#print axioms sourceMap4635_checked
#print axioms fusedMap4635_checked
#print axioms certified4635
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
