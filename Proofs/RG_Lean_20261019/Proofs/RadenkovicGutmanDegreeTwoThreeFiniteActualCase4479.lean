/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4479 : Family 10 := level10.get ⟨212,by decide⟩
def sourceMap4479 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4479 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4479_checked : acceptsGraphIso
    (source (graph core4479) (root 10) 2 2) DegreeTwoThreeSpectrum6168.graph sourceMap4479=true := by decide +kernel
theorem fusedMap4479_checked : acceptsGraphIso
    (fused (graph core4479) (root 10) 2 2) DegreeTwoThreeSpectrum5219.graph fusedMap4479=true := by decide +kernel
theorem certified4479 : Certified (graph core4479) (root 10) 2 2 :=
  of_native_maps core4479 DegreeTwoThreeSpectrum6168.graph DegreeTwoThreeSpectrum5219.graph
    sourceMap4479 fusedMap4479 sourceMap4479_checked fusedMap4479_checked
    DegreeTwoThreeFiniteComparisons.comparison4479
#print axioms sourceMap4479_checked
#print axioms fusedMap4479_checked
#print axioms certified4479
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
