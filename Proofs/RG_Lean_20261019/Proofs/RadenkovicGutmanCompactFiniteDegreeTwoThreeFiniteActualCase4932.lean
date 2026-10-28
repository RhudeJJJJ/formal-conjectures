/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4932 : Family 10 := level10.get ⟨1445,by decide⟩
def sourceMap4932 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap4932 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4932_checked : acceptsGraphIso
    (source (graph core4932) (root 10) 2 2) DegreeTwoThreeSpectrum7477.graph sourceMap4932=true := by decide +kernel
theorem fusedMap4932_checked : acceptsGraphIso
    (fused (graph core4932) (root 10) 2 2) DegreeTwoThreeSpectrum6909.graph fusedMap4932=true := by decide +kernel
theorem certified4932 : Certified (graph core4932) (root 10) 2 2 :=
  of_native_maps core4932 DegreeTwoThreeSpectrum7477.graph DegreeTwoThreeSpectrum6909.graph
    sourceMap4932 fusedMap4932 sourceMap4932_checked fusedMap4932_checked
    DegreeTwoThreeFiniteComparisons.comparison4932
#print axioms sourceMap4932_checked
#print axioms fusedMap4932_checked
#print axioms certified4932
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
