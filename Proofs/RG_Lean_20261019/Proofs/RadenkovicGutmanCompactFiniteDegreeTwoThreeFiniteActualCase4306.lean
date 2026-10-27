/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4306 : Family 9 := level9.get ⟨371,by decide⟩
def sourceMap4306 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4306 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4306_checked : acceptsGraphIso
    (source (graph core4306) (root 9) 2 2) DegreeTwoThreeSpectrum4741.graph sourceMap4306=true := by decide +kernel
theorem fusedMap4306_checked : acceptsGraphIso
    (fused (graph core4306) (root 9) 2 2) DegreeTwoThreeSpectrum4298.graph fusedMap4306=true := by decide +kernel
theorem certified4306 : Certified (graph core4306) (root 9) 2 2 :=
  of_native_maps core4306 DegreeTwoThreeSpectrum4741.graph DegreeTwoThreeSpectrum4298.graph
    sourceMap4306 fusedMap4306 sourceMap4306_checked fusedMap4306_checked
    DegreeTwoThreeFiniteComparisons.comparison4306
#print axioms sourceMap4306_checked
#print axioms fusedMap4306_checked
#print axioms certified4306
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
