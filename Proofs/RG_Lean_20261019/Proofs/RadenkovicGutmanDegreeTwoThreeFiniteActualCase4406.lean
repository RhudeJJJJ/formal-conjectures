/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4406 : Family 9 := level9.get ⟨608,by decide⟩
def sourceMap4406 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4406 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4406_checked : acceptsGraphIso
    (source (graph core4406) (root 9) 2 2) DegreeTwoThreeSpectrum4933.graph sourceMap4406=true := by decide +kernel
theorem fusedMap4406_checked : acceptsGraphIso
    (fused (graph core4406) (root 9) 2 2) DegreeTwoThreeSpectrum4303.graph fusedMap4406=true := by decide +kernel
theorem certified4406 : Certified (graph core4406) (root 9) 2 2 :=
  of_native_maps core4406 DegreeTwoThreeSpectrum4933.graph DegreeTwoThreeSpectrum4303.graph
    sourceMap4406 fusedMap4406 sourceMap4406_checked fusedMap4406_checked
    DegreeTwoThreeFiniteComparisons.comparison4406
#print axioms sourceMap4406_checked
#print axioms fusedMap4406_checked
#print axioms certified4406
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
