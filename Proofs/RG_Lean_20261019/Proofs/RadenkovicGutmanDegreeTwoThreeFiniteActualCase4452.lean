/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4452 : Family 10 := level10.get ⟨113,by decide⟩
def sourceMap4452 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4452 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4452_checked : acceptsGraphIso
    (source (graph core4452) (root 10) 2 2) DegreeTwoThreeSpectrum6788.graph sourceMap4452=true := by decide +kernel
theorem fusedMap4452_checked : acceptsGraphIso
    (fused (graph core4452) (root 10) 2 2) DegreeTwoThreeSpectrum5037.graph fusedMap4452=true := by decide +kernel
theorem certified4452 : Certified (graph core4452) (root 10) 2 2 :=
  of_native_maps core4452 DegreeTwoThreeSpectrum6788.graph DegreeTwoThreeSpectrum5037.graph
    sourceMap4452 fusedMap4452 sourceMap4452_checked fusedMap4452_checked
    DegreeTwoThreeFiniteComparisons.comparison4452
#print axioms sourceMap4452_checked
#print axioms fusedMap4452_checked
#print axioms certified4452
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
