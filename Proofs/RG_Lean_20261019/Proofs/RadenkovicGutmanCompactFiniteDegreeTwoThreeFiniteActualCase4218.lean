/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4218 : Family 9 := level9.get ⟨116,by decide⟩
def sourceMap4218 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4218 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4218_checked : acceptsGraphIso
    (source (graph core4218) (root 9) 2 2) DegreeTwoThreeSpectrum4554.graph sourceMap4218=true := by decide +kernel
theorem fusedMap4218_checked : acceptsGraphIso
    (fused (graph core4218) (root 9) 2 2) DegreeTwoThreeSpectrum4132.graph fusedMap4218=true := by decide +kernel
theorem certified4218 : Certified (graph core4218) (root 9) 2 2 :=
  of_native_maps core4218 DegreeTwoThreeSpectrum4554.graph DegreeTwoThreeSpectrum4132.graph
    sourceMap4218 fusedMap4218 sourceMap4218_checked fusedMap4218_checked
    DegreeTwoThreeFiniteComparisons.comparison4218
#print axioms sourceMap4218_checked
#print axioms fusedMap4218_checked
#print axioms certified4218
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
