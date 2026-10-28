/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4992 : Family 10 := level10.get ⟨1599,by decide⟩
def sourceMap4992 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4992 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4992_checked : acceptsGraphIso
    (source (graph core4992) (root 10) 2 2) DegreeTwoThreeSpectrum7593.graph sourceMap4992=true := by decide +kernel
theorem fusedMap4992_checked : acceptsGraphIso
    (fused (graph core4992) (root 10) 2 2) DegreeTwoThreeSpectrum6114.graph fusedMap4992=true := by decide +kernel
theorem certified4992 : Certified (graph core4992) (root 10) 2 2 :=
  of_native_maps core4992 DegreeTwoThreeSpectrum7593.graph DegreeTwoThreeSpectrum6114.graph
    sourceMap4992 fusedMap4992 sourceMap4992_checked fusedMap4992_checked
    DegreeTwoThreeFiniteComparisons.comparison4992
#print axioms sourceMap4992_checked
#print axioms fusedMap4992_checked
#print axioms certified4992
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
