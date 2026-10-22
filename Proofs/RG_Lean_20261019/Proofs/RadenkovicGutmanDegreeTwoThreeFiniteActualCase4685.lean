/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4685 : Family 10 := level10.get ⟨837,by decide⟩
def sourceMap4685 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4685 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4685_checked : acceptsGraphIso
    (source (graph core4685) (root 10) 2 2) DegreeTwoThreeSpectrum7501.graph sourceMap4685=true := by decide +kernel
theorem fusedMap4685_checked : acceptsGraphIso
    (fused (graph core4685) (root 10) 2 2) DegreeTwoThreeSpectrum5666.graph fusedMap4685=true := by decide +kernel
theorem certified4685 : Certified (graph core4685) (root 10) 2 2 :=
  of_native_maps core4685 DegreeTwoThreeSpectrum7501.graph DegreeTwoThreeSpectrum5666.graph
    sourceMap4685 fusedMap4685 sourceMap4685_checked fusedMap4685_checked
    DegreeTwoThreeFiniteComparisons.comparison4685
#print axioms sourceMap4685_checked
#print axioms fusedMap4685_checked
#print axioms certified4685
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
