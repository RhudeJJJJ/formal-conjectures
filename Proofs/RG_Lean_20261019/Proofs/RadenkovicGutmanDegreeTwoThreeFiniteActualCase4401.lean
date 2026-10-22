/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4401 : Family 9 := level9.get ⟨597,by decide⟩
def sourceMap4401 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4401 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4401_checked : acceptsGraphIso
    (source (graph core4401) (root 9) 2 2) DegreeTwoThreeSpectrum4928.graph sourceMap4401=true := by decide +kernel
theorem fusedMap4401_checked : acceptsGraphIso
    (fused (graph core4401) (root 9) 2 2) DegreeTwoThreeSpectrum4276.graph fusedMap4401=true := by decide +kernel
theorem certified4401 : Certified (graph core4401) (root 9) 2 2 :=
  of_native_maps core4401 DegreeTwoThreeSpectrum4928.graph DegreeTwoThreeSpectrum4276.graph
    sourceMap4401 fusedMap4401 sourceMap4401_checked fusedMap4401_checked
    DegreeTwoThreeFiniteComparisons.comparison4401
#print axioms sourceMap4401_checked
#print axioms fusedMap4401_checked
#print axioms certified4401
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
