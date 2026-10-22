/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4343 : Family 9 := level9.get ⟨463,by decide⟩
def sourceMap4343 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4343 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4343_checked : acceptsGraphIso
    (source (graph core4343) (root 9) 2 2) DegreeTwoThreeSpectrum4844.graph sourceMap4343=true := by decide +kernel
theorem fusedMap4343_checked : acceptsGraphIso
    (fused (graph core4343) (root 9) 2 2) DegreeTwoThreeSpectrum4493.graph fusedMap4343=true := by decide +kernel
theorem certified4343 : Certified (graph core4343) (root 9) 2 2 :=
  of_native_maps core4343 DegreeTwoThreeSpectrum4844.graph DegreeTwoThreeSpectrum4493.graph
    sourceMap4343 fusedMap4343 sourceMap4343_checked fusedMap4343_checked
    DegreeTwoThreeFiniteComparisons.comparison4343
#print axioms sourceMap4343_checked
#print axioms fusedMap4343_checked
#print axioms certified4343
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
