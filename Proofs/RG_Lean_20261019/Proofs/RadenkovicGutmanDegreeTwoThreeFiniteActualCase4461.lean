/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4461 : Family 10 := level10.get ⟨150,by decide⟩
def sourceMap4461 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4461 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4461_checked : acceptsGraphIso
    (source (graph core4461) (root 10) 2 2) DegreeTwoThreeSpectrum6852.graph sourceMap4461=true := by decide +kernel
theorem fusedMap4461_checked : acceptsGraphIso
    (fused (graph core4461) (root 10) 2 2) DegreeTwoThreeSpectrum5086.graph fusedMap4461=true := by decide +kernel
theorem certified4461 : Certified (graph core4461) (root 10) 2 2 :=
  of_native_maps core4461 DegreeTwoThreeSpectrum6852.graph DegreeTwoThreeSpectrum5086.graph
    sourceMap4461 fusedMap4461 sourceMap4461_checked fusedMap4461_checked
    DegreeTwoThreeFiniteComparisons.comparison4461
#print axioms sourceMap4461_checked
#print axioms fusedMap4461_checked
#print axioms certified4461
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
