/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4499 : Family 10 := level10.get ⟨280,by decide⟩
def sourceMap4499 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4499 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4499_checked : acceptsGraphIso
    (source (graph core4499) (root 10) 2 2) DegreeTwoThreeSpectrum6454.graph sourceMap4499=true := by decide +kernel
theorem fusedMap4499_checked : acceptsGraphIso
    (fused (graph core4499) (root 10) 2 2) DegreeTwoThreeSpectrum5418.graph fusedMap4499=true := by decide +kernel
theorem certified4499 : Certified (graph core4499) (root 10) 2 2 :=
  of_native_maps core4499 DegreeTwoThreeSpectrum6454.graph DegreeTwoThreeSpectrum5418.graph
    sourceMap4499 fusedMap4499 sourceMap4499_checked fusedMap4499_checked
    DegreeTwoThreeFiniteComparisons.comparison4499
#print axioms sourceMap4499_checked
#print axioms fusedMap4499_checked
#print axioms certified4499
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
