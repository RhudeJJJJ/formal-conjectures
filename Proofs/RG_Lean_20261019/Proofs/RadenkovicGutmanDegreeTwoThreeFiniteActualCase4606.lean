/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4606 : Family 10 := level10.get ⟨619,by decide⟩
def sourceMap4606 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4606 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4606_checked : acceptsGraphIso
    (source (graph core4606) (root 10) 2 2) DegreeTwoThreeSpectrum7277.graph sourceMap4606=true := by decide +kernel
theorem fusedMap4606_checked : acceptsGraphIso
    (fused (graph core4606) (root 10) 2 2) DegreeTwoThreeSpectrum5309.graph fusedMap4606=true := by decide +kernel
theorem certified4606 : Certified (graph core4606) (root 10) 2 2 :=
  of_native_maps core4606 DegreeTwoThreeSpectrum7277.graph DegreeTwoThreeSpectrum5309.graph
    sourceMap4606 fusedMap4606 sourceMap4606_checked fusedMap4606_checked
    DegreeTwoThreeFiniteComparisons.comparison4606
#print axioms sourceMap4606_checked
#print axioms fusedMap4606_checked
#print axioms certified4606
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
