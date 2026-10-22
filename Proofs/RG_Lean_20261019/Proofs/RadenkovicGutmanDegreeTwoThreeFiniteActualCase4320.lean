/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4320 : Family 9 := level9.get ⟨403,by decide⟩
def sourceMap4320 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4320 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4320_checked : acceptsGraphIso
    (source (graph core4320) (root 9) 2 2) DegreeTwoThreeSpectrum4778.graph sourceMap4320=true := by decide +kernel
theorem fusedMap4320_checked : acceptsGraphIso
    (fused (graph core4320) (root 9) 2 2) DegreeTwoThreeSpectrum4362.graph fusedMap4320=true := by decide +kernel
theorem certified4320 : Certified (graph core4320) (root 9) 2 2 :=
  of_native_maps core4320 DegreeTwoThreeSpectrum4778.graph DegreeTwoThreeSpectrum4362.graph
    sourceMap4320 fusedMap4320 sourceMap4320_checked fusedMap4320_checked
    DegreeTwoThreeFiniteComparisons.comparison4320
#print axioms sourceMap4320_checked
#print axioms fusedMap4320_checked
#print axioms certified4320
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
