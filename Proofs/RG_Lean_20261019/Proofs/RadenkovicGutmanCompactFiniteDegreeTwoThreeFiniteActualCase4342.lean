/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4342 : Family 9 := level9.get ⟨460,by decide⟩
def sourceMap4342 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4342 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4342_checked : acceptsGraphIso
    (source (graph core4342) (root 9) 2 2) DegreeTwoThreeSpectrum4841.graph sourceMap4342=true := by decide +kernel
theorem fusedMap4342_checked : acceptsGraphIso
    (fused (graph core4342) (root 9) 2 2) DegreeTwoThreeSpectrum4486.graph fusedMap4342=true := by decide +kernel
theorem certified4342 : Certified (graph core4342) (root 9) 2 2 :=
  of_native_maps core4342 DegreeTwoThreeSpectrum4841.graph DegreeTwoThreeSpectrum4486.graph
    sourceMap4342 fusedMap4342 sourceMap4342_checked fusedMap4342_checked
    DegreeTwoThreeFiniteComparisons.comparison4342
#print axioms sourceMap4342_checked
#print axioms fusedMap4342_checked
#print axioms certified4342
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
