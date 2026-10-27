/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4361 : Family 9 := level9.get ⟨503,by decide⟩
def sourceMap4361 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4361 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4361_checked : acceptsGraphIso
    (source (graph core4361) (root 9) 2 2) DegreeTwoThreeSpectrum4875.graph sourceMap4361=true := by decide +kernel
theorem fusedMap4361_checked : acceptsGraphIso
    (fused (graph core4361) (root 9) 2 2) DegreeTwoThreeSpectrum4582.graph fusedMap4361=true := by decide +kernel
theorem certified4361 : Certified (graph core4361) (root 9) 2 2 :=
  of_native_maps core4361 DegreeTwoThreeSpectrum4875.graph DegreeTwoThreeSpectrum4582.graph
    sourceMap4361 fusedMap4361 sourceMap4361_checked fusedMap4361_checked
    DegreeTwoThreeFiniteComparisons.comparison4361
#print axioms sourceMap4361_checked
#print axioms fusedMap4361_checked
#print axioms certified4361
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
