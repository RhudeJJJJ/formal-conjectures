/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4862 : Family 10 := level10.get ⟨1282,by decide⟩
def sourceMap4862 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4862 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4862_checked : acceptsGraphIso
    (source (graph core4862) (root 10) 2 2) DegreeTwoThreeSpectrum7364.graph sourceMap4862=true := by decide +kernel
theorem fusedMap4862_checked : acceptsGraphIso
    (fused (graph core4862) (root 10) 2 2) DegreeTwoThreeSpectrum6549.graph fusedMap4862=true := by decide +kernel
theorem certified4862 : Certified (graph core4862) (root 10) 2 2 :=
  of_native_maps core4862 DegreeTwoThreeSpectrum7364.graph DegreeTwoThreeSpectrum6549.graph
    sourceMap4862 fusedMap4862 sourceMap4862_checked fusedMap4862_checked
    DegreeTwoThreeFiniteComparisons.comparison4862
#print axioms sourceMap4862_checked
#print axioms fusedMap4862_checked
#print axioms certified4862
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
