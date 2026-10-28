/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4917 : Family 10 := level10.get ⟨1411,by decide⟩
def sourceMap4917 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4917 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4917_checked : acceptsGraphIso
    (source (graph core4917) (root 10) 2 2) DegreeTwoThreeSpectrum7500.graph sourceMap4917=true := by decide +kernel
theorem fusedMap4917_checked : acceptsGraphIso
    (fused (graph core4917) (root 10) 2 2) DegreeTwoThreeSpectrum6824.graph fusedMap4917=true := by decide +kernel
theorem certified4917 : Certified (graph core4917) (root 10) 2 2 :=
  of_native_maps core4917 DegreeTwoThreeSpectrum7500.graph DegreeTwoThreeSpectrum6824.graph
    sourceMap4917 fusedMap4917 sourceMap4917_checked fusedMap4917_checked
    DegreeTwoThreeFiniteComparisons.comparison4917
#print axioms sourceMap4917_checked
#print axioms fusedMap4917_checked
#print axioms certified4917
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
