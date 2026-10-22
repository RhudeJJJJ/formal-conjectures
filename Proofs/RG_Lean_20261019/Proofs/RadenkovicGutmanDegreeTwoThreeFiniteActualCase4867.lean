/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4867 : Family 10 := level10.get ⟨1290,by decide⟩
def sourceMap4867 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4867 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4867_checked : acceptsGraphIso
    (source (graph core4867) (root 10) 2 2) DegreeTwoThreeSpectrum7370.graph sourceMap4867=true := by decide +kernel
theorem fusedMap4867_checked : acceptsGraphIso
    (fused (graph core4867) (root 10) 2 2) DegreeTwoThreeSpectrum6565.graph fusedMap4867=true := by decide +kernel
theorem certified4867 : Certified (graph core4867) (root 10) 2 2 :=
  of_native_maps core4867 DegreeTwoThreeSpectrum7370.graph DegreeTwoThreeSpectrum6565.graph
    sourceMap4867 fusedMap4867 sourceMap4867_checked fusedMap4867_checked
    DegreeTwoThreeFiniteComparisons.comparison4867
#print axioms sourceMap4867_checked
#print axioms fusedMap4867_checked
#print axioms certified4867
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
