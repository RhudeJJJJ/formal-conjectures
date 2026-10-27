/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4746 : Family 10 := level10.get ⟨983,by decide⟩
def sourceMap4746 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,13,14,15,16,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4746 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4746_checked : acceptsGraphIso
    (source (graph core4746) (root 10) 2 2) DegreeTwoThreeSpectrum7355.graph sourceMap4746=true := by decide +kernel
theorem fusedMap4746_checked : acceptsGraphIso
    (fused (graph core4746) (root 10) 2 2) DegreeTwoThreeSpectrum5919.graph fusedMap4746=true := by decide +kernel
theorem certified4746 : Certified (graph core4746) (root 10) 2 2 :=
  of_native_maps core4746 DegreeTwoThreeSpectrum7355.graph DegreeTwoThreeSpectrum5919.graph
    sourceMap4746 fusedMap4746 sourceMap4746_checked fusedMap4746_checked
    DegreeTwoThreeFiniteComparisons.comparison4746
#print axioms sourceMap4746_checked
#print axioms fusedMap4746_checked
#print axioms certified4746
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
