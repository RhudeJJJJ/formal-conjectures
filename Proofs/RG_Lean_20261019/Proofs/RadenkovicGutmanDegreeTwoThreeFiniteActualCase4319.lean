/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4319 : Family 9 := level9.get ⟨402,by decide⟩
def sourceMap4319 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4319 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4319_checked : acceptsGraphIso
    (source (graph core4319) (root 9) 2 2) DegreeTwoThreeSpectrum4777.graph sourceMap4319=true := by decide +kernel
theorem fusedMap4319_checked : acceptsGraphIso
    (fused (graph core4319) (root 9) 2 2) DegreeTwoThreeSpectrum4360.graph fusedMap4319=true := by decide +kernel
theorem certified4319 : Certified (graph core4319) (root 9) 2 2 :=
  of_native_maps core4319 DegreeTwoThreeSpectrum4777.graph DegreeTwoThreeSpectrum4360.graph
    sourceMap4319 fusedMap4319 sourceMap4319_checked fusedMap4319_checked
    DegreeTwoThreeFiniteComparisons.comparison4319
#print axioms sourceMap4319_checked
#print axioms fusedMap4319_checked
#print axioms certified4319
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
