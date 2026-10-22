/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4967 : Family 10 := level10.get ⟨1544,by decide⟩
def sourceMap4967 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4967 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4967_checked : acceptsGraphIso
    (source (graph core4967) (root 10) 2 2) DegreeTwoThreeSpectrum7568.graph sourceMap4967=true := by decide +kernel
theorem fusedMap4967_checked : acceptsGraphIso
    (fused (graph core4967) (root 10) 2 2) DegreeTwoThreeSpectrum5995.graph fusedMap4967=true := by decide +kernel
theorem certified4967 : Certified (graph core4967) (root 10) 2 2 :=
  of_native_maps core4967 DegreeTwoThreeSpectrum7568.graph DegreeTwoThreeSpectrum5995.graph
    sourceMap4967 fusedMap4967 sourceMap4967_checked fusedMap4967_checked
    DegreeTwoThreeFiniteComparisons.comparison4967
#print axioms sourceMap4967_checked
#print axioms fusedMap4967_checked
#print axioms certified4967
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
