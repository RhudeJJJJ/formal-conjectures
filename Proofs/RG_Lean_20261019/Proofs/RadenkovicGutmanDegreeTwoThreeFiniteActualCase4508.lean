/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4508 : Family 10 := level10.get ⟨317,by decide⟩
def sourceMap4508 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4508 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4508_checked : acceptsGraphIso
    (source (graph core4508) (root 10) 2 2) DegreeTwoThreeSpectrum6666.graph sourceMap4508=true := by decide +kernel
theorem fusedMap4508_checked : acceptsGraphIso
    (fused (graph core4508) (root 10) 2 2) DegreeTwoThreeSpectrum5528.graph fusedMap4508=true := by decide +kernel
theorem certified4508 : Certified (graph core4508) (root 10) 2 2 :=
  of_native_maps core4508 DegreeTwoThreeSpectrum6666.graph DegreeTwoThreeSpectrum5528.graph
    sourceMap4508 fusedMap4508 sourceMap4508_checked fusedMap4508_checked
    DegreeTwoThreeFiniteComparisons.comparison4508
#print axioms sourceMap4508_checked
#print axioms fusedMap4508_checked
#print axioms certified4508
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
