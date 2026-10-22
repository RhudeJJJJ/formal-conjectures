/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4937 : Family 10 := level10.get ⟨1453,by decide⟩
def sourceMap4937 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,7,8,9,10,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4937 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4937_checked : acceptsGraphIso
    (source (graph core4937) (root 10) 2 2) DegreeTwoThreeSpectrum7487.graph sourceMap4937=true := by decide +kernel
theorem fusedMap4937_checked : acceptsGraphIso
    (fused (graph core4937) (root 10) 2 2) DegreeTwoThreeSpectrum6924.graph fusedMap4937=true := by decide +kernel
theorem certified4937 : Certified (graph core4937) (root 10) 2 2 :=
  of_native_maps core4937 DegreeTwoThreeSpectrum7487.graph DegreeTwoThreeSpectrum6924.graph
    sourceMap4937 fusedMap4937 sourceMap4937_checked fusedMap4937_checked
    DegreeTwoThreeFiniteComparisons.comparison4937
#print axioms sourceMap4937_checked
#print axioms fusedMap4937_checked
#print axioms certified4937
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
