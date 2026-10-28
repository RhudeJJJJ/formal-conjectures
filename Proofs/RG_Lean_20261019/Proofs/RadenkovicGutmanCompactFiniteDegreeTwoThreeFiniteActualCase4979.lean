/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4979 : Family 10 := level10.get ⟨1571,by decide⟩
def sourceMap4979 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4979 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4979_checked : acceptsGraphIso
    (source (graph core4979) (root 10) 2 2) DegreeTwoThreeSpectrum7580.graph sourceMap4979=true := by decide +kernel
theorem fusedMap4979_checked : acceptsGraphIso
    (fused (graph core4979) (root 10) 2 2) DegreeTwoThreeSpectrum6050.graph fusedMap4979=true := by decide +kernel
theorem certified4979 : Certified (graph core4979) (root 10) 2 2 :=
  of_native_maps core4979 DegreeTwoThreeSpectrum7580.graph DegreeTwoThreeSpectrum6050.graph
    sourceMap4979 fusedMap4979 sourceMap4979_checked fusedMap4979_checked
    DegreeTwoThreeFiniteComparisons.comparison4979
#print axioms sourceMap4979_checked
#print axioms fusedMap4979_checked
#print axioms certified4979
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
