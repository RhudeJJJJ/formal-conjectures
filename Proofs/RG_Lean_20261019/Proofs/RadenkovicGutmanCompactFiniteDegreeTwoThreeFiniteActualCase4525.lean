/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4525 : Family 10 := level10.get ⟨370,by decide⟩
def sourceMap4525 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4525 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4525_checked : acceptsGraphIso
    (source (graph core4525) (root 10) 2 2) DegreeTwoThreeSpectrum6837.graph sourceMap4525=true := by decide +kernel
theorem fusedMap4525_checked : acceptsGraphIso
    (fused (graph core4525) (root 10) 2 2) DegreeTwoThreeSpectrum5670.graph fusedMap4525=true := by decide +kernel
theorem certified4525 : Certified (graph core4525) (root 10) 2 2 :=
  of_native_maps core4525 DegreeTwoThreeSpectrum6837.graph DegreeTwoThreeSpectrum5670.graph
    sourceMap4525 fusedMap4525 sourceMap4525_checked fusedMap4525_checked
    DegreeTwoThreeFiniteComparisons.comparison4525
#print axioms sourceMap4525_checked
#print axioms fusedMap4525_checked
#print axioms certified4525
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
