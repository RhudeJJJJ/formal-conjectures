/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4909 : Family 10 := level10.get ⟨1388,by decide⟩
def sourceMap4909 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4909 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4909_checked : acceptsGraphIso
    (source (graph core4909) (root 10) 2 2) DegreeTwoThreeSpectrum7474.graph sourceMap4909=true := by decide +kernel
theorem fusedMap4909_checked : acceptsGraphIso
    (fused (graph core4909) (root 10) 2 2) DegreeTwoThreeSpectrum6750.graph fusedMap4909=true := by decide +kernel
theorem certified4909 : Certified (graph core4909) (root 10) 2 2 :=
  of_native_maps core4909 DegreeTwoThreeSpectrum7474.graph DegreeTwoThreeSpectrum6750.graph
    sourceMap4909 fusedMap4909 sourceMap4909_checked fusedMap4909_checked
    DegreeTwoThreeFiniteComparisons.comparison4909
#print axioms sourceMap4909_checked
#print axioms fusedMap4909_checked
#print axioms certified4909
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
