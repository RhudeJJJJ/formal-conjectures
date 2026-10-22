/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4956 : Family 10 := level10.get ⟨1502,by decide⟩
def sourceMap4956 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4956 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4956_checked : acceptsGraphIso
    (source (graph core4956) (root 10) 2 2) DegreeTwoThreeSpectrum7340.graph sourceMap4956=true := by decide +kernel
theorem fusedMap4956_checked : acceptsGraphIso
    (fused (graph core4956) (root 10) 2 2) DegreeTwoThreeSpectrum7008.graph fusedMap4956=true := by decide +kernel
theorem certified4956 : Certified (graph core4956) (root 10) 2 2 :=
  of_native_maps core4956 DegreeTwoThreeSpectrum7340.graph DegreeTwoThreeSpectrum7008.graph
    sourceMap4956 fusedMap4956 sourceMap4956_checked fusedMap4956_checked
    DegreeTwoThreeFiniteComparisons.comparison4956
#print axioms sourceMap4956_checked
#print axioms fusedMap4956_checked
#print axioms certified4956
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
