/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4948 : Family 10 := level10.get ⟨1478,by decide⟩
def sourceMap4948 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4948 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4948_checked : acceptsGraphIso
    (source (graph core4948) (root 10) 2 2) DegreeTwoThreeSpectrum7233.graph sourceMap4948=true := by decide +kernel
theorem fusedMap4948_checked : acceptsGraphIso
    (fused (graph core4948) (root 10) 2 2) DegreeTwoThreeSpectrum6966.graph fusedMap4948=true := by decide +kernel
theorem certified4948 : Certified (graph core4948) (root 10) 2 2 :=
  of_native_maps core4948 DegreeTwoThreeSpectrum7233.graph DegreeTwoThreeSpectrum6966.graph
    sourceMap4948 fusedMap4948 sourceMap4948_checked fusedMap4948_checked
    DegreeTwoThreeFiniteComparisons.comparison4948
#print axioms sourceMap4948_checked
#print axioms fusedMap4948_checked
#print axioms certified4948
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
