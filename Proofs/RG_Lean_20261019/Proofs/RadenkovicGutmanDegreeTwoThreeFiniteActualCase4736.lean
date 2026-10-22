/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4736 : Family 10 := level10.get ⟨966,by decide⟩
def sourceMap4736 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4736 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4736_checked : acceptsGraphIso
    (source (graph core4736) (root 10) 2 2) DegreeTwoThreeSpectrum7015.graph sourceMap4736=true := by decide +kernel
theorem fusedMap4736_checked : acceptsGraphIso
    (fused (graph core4736) (root 10) 2 2) DegreeTwoThreeSpectrum5885.graph fusedMap4736=true := by decide +kernel
theorem certified4736 : Certified (graph core4736) (root 10) 2 2 :=
  of_native_maps core4736 DegreeTwoThreeSpectrum7015.graph DegreeTwoThreeSpectrum5885.graph
    sourceMap4736 fusedMap4736 sourceMap4736_checked fusedMap4736_checked
    DegreeTwoThreeFiniteComparisons.comparison4736
#print axioms sourceMap4736_checked
#print axioms fusedMap4736_checked
#print axioms certified4736
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
