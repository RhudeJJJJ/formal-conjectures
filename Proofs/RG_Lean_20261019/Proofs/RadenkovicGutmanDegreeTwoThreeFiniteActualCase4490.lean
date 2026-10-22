/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4490 : Family 10 := level10.get ⟨256,by decide⟩
def sourceMap4490 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4490 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4490_checked : acceptsGraphIso
    (source (graph core4490) (root 10) 2 2) DegreeTwoThreeSpectrum6414.graph sourceMap4490=true := by decide +kernel
theorem fusedMap4490_checked : acceptsGraphIso
    (fused (graph core4490) (root 10) 2 2) DegreeTwoThreeSpectrum5357.graph fusedMap4490=true := by decide +kernel
theorem certified4490 : Certified (graph core4490) (root 10) 2 2 :=
  of_native_maps core4490 DegreeTwoThreeSpectrum6414.graph DegreeTwoThreeSpectrum5357.graph
    sourceMap4490 fusedMap4490 sourceMap4490_checked fusedMap4490_checked
    DegreeTwoThreeFiniteComparisons.comparison4490
#print axioms sourceMap4490_checked
#print axioms fusedMap4490_checked
#print axioms certified4490
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
