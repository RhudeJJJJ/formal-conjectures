/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4520 : Family 10 := level10.get ⟨358,by decide⟩
def sourceMap4520 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4520 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4520_checked : acceptsGraphIso
    (source (graph core4520) (root 10) 2 2) DegreeTwoThreeSpectrum6785.graph sourceMap4520=true := by decide +kernel
theorem fusedMap4520_checked : acceptsGraphIso
    (fused (graph core4520) (root 10) 2 2) DegreeTwoThreeSpectrum5640.graph fusedMap4520=true := by decide +kernel
theorem certified4520 : Certified (graph core4520) (root 10) 2 2 :=
  of_native_maps core4520 DegreeTwoThreeSpectrum6785.graph DegreeTwoThreeSpectrum5640.graph
    sourceMap4520 fusedMap4520 sourceMap4520_checked fusedMap4520_checked
    DegreeTwoThreeFiniteComparisons.comparison4520
#print axioms sourceMap4520_checked
#print axioms fusedMap4520_checked
#print axioms certified4520
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
