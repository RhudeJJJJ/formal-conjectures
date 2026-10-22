/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4619 : Family 10 := level10.get ⟨657,by decide⟩
def sourceMap4619 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4619 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4619_checked : acceptsGraphIso
    (source (graph core4619) (root 10) 2 2) DegreeTwoThreeSpectrum7317.graph sourceMap4619=true := by decide +kernel
theorem fusedMap4619_checked : acceptsGraphIso
    (fused (graph core4619) (root 10) 2 2) DegreeTwoThreeSpectrum5366.graph fusedMap4619=true := by decide +kernel
theorem certified4619 : Certified (graph core4619) (root 10) 2 2 :=
  of_native_maps core4619 DegreeTwoThreeSpectrum7317.graph DegreeTwoThreeSpectrum5366.graph
    sourceMap4619 fusedMap4619 sourceMap4619_checked fusedMap4619_checked
    DegreeTwoThreeFiniteComparisons.comparison4619
#print axioms sourceMap4619_checked
#print axioms fusedMap4619_checked
#print axioms certified4619
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
