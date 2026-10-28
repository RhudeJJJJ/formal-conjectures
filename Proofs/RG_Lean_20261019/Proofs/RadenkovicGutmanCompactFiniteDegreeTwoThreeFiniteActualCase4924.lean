/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4924 : Family 10 := level10.get ⟨1429,by decide⟩
def sourceMap4924 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,8,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4924 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4924_checked : acceptsGraphIso
    (source (graph core4924) (root 10) 2 2) DegreeTwoThreeSpectrum7525.graph sourceMap4924=true := by decide +kernel
theorem fusedMap4924_checked : acceptsGraphIso
    (fused (graph core4924) (root 10) 2 2) DegreeTwoThreeSpectrum6884.graph fusedMap4924=true := by decide +kernel
theorem certified4924 : Certified (graph core4924) (root 10) 2 2 :=
  of_native_maps core4924 DegreeTwoThreeSpectrum7525.graph DegreeTwoThreeSpectrum6884.graph
    sourceMap4924 fusedMap4924 sourceMap4924_checked fusedMap4924_checked
    DegreeTwoThreeFiniteComparisons.comparison4924
#print axioms sourceMap4924_checked
#print axioms fusedMap4924_checked
#print axioms certified4924
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
