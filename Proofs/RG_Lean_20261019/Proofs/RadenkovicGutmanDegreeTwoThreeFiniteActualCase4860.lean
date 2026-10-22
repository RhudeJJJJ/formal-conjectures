/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4860 : Family 10 := level10.get ⟨1278,by decide⟩
def sourceMap4860 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4860 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4860_checked : acceptsGraphIso
    (source (graph core4860) (root 10) 2 2) DegreeTwoThreeSpectrum7361.graph sourceMap4860=true := by decide +kernel
theorem fusedMap4860_checked : acceptsGraphIso
    (fused (graph core4860) (root 10) 2 2) DegreeTwoThreeSpectrum6543.graph fusedMap4860=true := by decide +kernel
theorem certified4860 : Certified (graph core4860) (root 10) 2 2 :=
  of_native_maps core4860 DegreeTwoThreeSpectrum7361.graph DegreeTwoThreeSpectrum6543.graph
    sourceMap4860 fusedMap4860 sourceMap4860_checked fusedMap4860_checked
    DegreeTwoThreeFiniteComparisons.comparison4860
#print axioms sourceMap4860_checked
#print axioms fusedMap4860_checked
#print axioms certified4860
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
