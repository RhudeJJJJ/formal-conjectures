/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4086 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap4086 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,11,12,13,5,6,7,8,9,10] (sourceLabel 7 2 2 v)
def fusedMap4086 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4086_checked : acceptsGraphIso
    (source (graph core4086) (root 7) 2 2) DegreeTwoThreeSpectrum2284.graph sourceMap4086=true := by decide +kernel
theorem fusedMap4086_checked : acceptsGraphIso
    (fused (graph core4086) (root 7) 2 2) DegreeTwoThreeSpectrum1776.graph fusedMap4086=true := by decide +kernel
theorem certified4086 : Certified (graph core4086) (root 7) 2 2 :=
  of_native_maps core4086 DegreeTwoThreeSpectrum2284.graph DegreeTwoThreeSpectrum1776.graph
    sourceMap4086 fusedMap4086 sourceMap4086_checked fusedMap4086_checked
    DegreeTwoThreeFiniteComparisons.comparison4086
#print axioms sourceMap4086_checked
#print axioms fusedMap4086_checked
#print axioms certified4086
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
