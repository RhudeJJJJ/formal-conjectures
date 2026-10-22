/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4482 : Family 10 := level10.get ⟨225,by decide⟩
def sourceMap4482 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4482 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4482_checked : acceptsGraphIso
    (source (graph core4482) (root 10) 2 2) DegreeTwoThreeSpectrum6276.graph sourceMap4482=true := by decide +kernel
theorem fusedMap4482_checked : acceptsGraphIso
    (fused (graph core4482) (root 10) 2 2) DegreeTwoThreeSpectrum5263.graph fusedMap4482=true := by decide +kernel
theorem certified4482 : Certified (graph core4482) (root 10) 2 2 :=
  of_native_maps core4482 DegreeTwoThreeSpectrum6276.graph DegreeTwoThreeSpectrum5263.graph
    sourceMap4482 fusedMap4482 sourceMap4482_checked fusedMap4482_checked
    DegreeTwoThreeFiniteComparisons.comparison4482
#print axioms sourceMap4482_checked
#print axioms fusedMap4482_checked
#print axioms certified4482
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
