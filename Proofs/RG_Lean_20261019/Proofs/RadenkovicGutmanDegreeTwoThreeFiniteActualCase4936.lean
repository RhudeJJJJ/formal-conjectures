/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4936 : Family 10 := level10.get ⟨1451,by decide⟩
def sourceMap4936 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4936 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4936_checked : acceptsGraphIso
    (source (graph core4936) (root 10) 2 2) DegreeTwoThreeSpectrum7428.graph sourceMap4936=true := by decide +kernel
theorem fusedMap4936_checked : acceptsGraphIso
    (fused (graph core4936) (root 10) 2 2) DegreeTwoThreeSpectrum6920.graph fusedMap4936=true := by decide +kernel
theorem certified4936 : Certified (graph core4936) (root 10) 2 2 :=
  of_native_maps core4936 DegreeTwoThreeSpectrum7428.graph DegreeTwoThreeSpectrum6920.graph
    sourceMap4936 fusedMap4936 sourceMap4936_checked fusedMap4936_checked
    DegreeTwoThreeFiniteComparisons.comparison4936
#print axioms sourceMap4936_checked
#print axioms fusedMap4936_checked
#print axioms certified4936
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
